/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeActionTransition
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem125
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1211
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Lemma1217
import OddOrder.BG.Ch3_MaximalSubgroups.S14_Prop142Support
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310
import OddOrder.GroupTheory.MaximalSubgroupType
import OddOrder.GroupTheory.MaximalSubgroupTypeConj
import OddOrder.GroupTheory.PiElementDecomposition

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

/-! ## Derived subgroup of a split extension (general group theory)

Used for BG Theorem 14.7(h): if `M = M_σ ⋊ E` and `M_σ ≤ M'`, then `M' = M_σ ⊔ E'`, so the
type-`P` complement structure reduces to `E = K ⋉ E'` inside the `σ(M)'`-complement `E`. -/

open scoped commutatorElement in
/-- **Derived subgroup of a split extension**: if `N ⊴ H` has a complement `E`
(`H = N ⋊ E`) and `N ≤ H'`, then `H' = N ⊔ ⁅E, E⁆`.

`N ⊔ ⁅E,E⁆ ≤ H'` is immediate (`N ≤ H'` by hypothesis, `⁅E,E⁆ ≤ ⁅⊤,⊤⁆ = H'`).  For
`H' ≤ N ⊔ ⁅E,E⁆`, every commutator `⁅n₁e₁, n₂e₂⁆` is congruent mod `N` to `⁅e₁,e₂⁆ ∈ ⁅E,E⁆`
(pushing through `H ↠ H/N` kills the `N`-factors), and `N ⊴ H` makes `N · ⁅E,E⁆` a subgroup. -/
theorem commutator_eq_sup_commutator_of_isComplement' {H : Type*} [Group H]
    {N E : Subgroup H} [N.Normal] (hcompl : N.IsComplement' E)
    (hNle : N ≤ commutator H) :
    commutator H = N ⊔ ⁅E, E⁆ := by
  have hsup : N ⊔ E = ⊤ := hcompl.sup_eq_top
  refine le_antisymm ?_ (sup_le hNle ?_)
  · -- `H' = ⁅⊤,⊤⁆ ≤ N ⊔ ⁅E,E⁆`.
    rw [commutator_def, ← hsup, Subgroup.commutator_le]
    intro a ha b hb
    -- Decompose `a = n₁ e₁`, `b = n₂ e₂` using `N ⊴ H`.
    obtain ⟨n₁, hn₁, e₁, he₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    obtain ⟨n₂, hn₂, e₂, he₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    -- `⁅n₁e₁, n₂e₂⁆ ≡ ⁅e₁,e₂⁆  (mod N)`, via `H ↠ H/N`.
    have hmod : ⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹ ∈ N := by
      have hf₁ : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
      have hf₂ : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
      have key : (QuotientGroup.mk' N) (⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹) = 1 := by
        simp only [map_mul, map_inv, map_commutatorElement, hf₁, hf₂, one_mul, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp (by rwa [QuotientGroup.mk'_apply] at key)
    -- `⁅n₁e₁, n₂e₂⁆ = (⁅n₁e₁,n₂e₂⁆ ⁅e₁,e₂⁆⁻¹) · ⁅e₁,e₂⁆ ∈ N · ⁅E,E⁆ ⊆ N ⊔ ⁅E,E⁆`.
    have heq : ⁅n₁ * e₁, n₂ * e₂⁆ = (⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹) * ⁅e₁, e₂⁆ := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmod)
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator he₁ he₂))
  · -- `⁅E,E⁆ ≤ ⁅⊤,⊤⁆ = H'`.
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top

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
  {p | p.Prime ∧ p ∈ tau1 M ∪ tau3 M ∧
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

/-- `κ(M) ⊆ τ₁(M) ∪ τ₃(M)`, directly from the definition of `κ`.  Used in Proposition 14.2:
a Hall `κ(M)`-subgroup is a `σ(M)'`-subgroup (since `τ₁, τ₃ ⊆ σ(M)'`), so the §12 `E`-setup
may be chosen to contain it. -/
theorem kappa_subset_tau1_union_tau3 {M : Subgroup G} : kappa M ⊆ tau1 M ∪ tau3 M :=
  fun _ hp => hp.2.1

/-- Every prime in `κ(M)` is prime (recorded explicitly in the definition). -/
theorem prime_of_mem_kappa {M : Subgroup G} {p : ℕ} (hp : p ∈ kappa M) : p.Prime := hp.1

/-- `κ(M) ⊆ σ(M)'`: a Hall `κ(M)`-subgroup is a `σ(M)'`-subgroup (since `τ₁, τ₃ ⊆ σ(M)'`).
This lets Proposition 14.2 feed a Hall `κ(M)`-subgroup `K` to `exists_subgroupESetup_with_le`
to obtain an `E`-setup with `K ≤ E`. -/
theorem kappa_subset_sigmaCompl {M : Subgroup G} : kappa M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
  intro p hp
  rcases kappa_subset_tau1_union_tau3 hp with h | h
  · exact ((mem_tau1_iff M p).mp h).1
  · exact ((mem_tau3_iff M p).mp h).1

/-- `κ(M) ⊆ π(M) ∖ σ(M)` (`sigmaComplementPrimes M`): a `κ`-prime divides `|M|` (it carries a
rank-one elementary abelian witness `P ≤ M` of order `p`) and lies outside `σ(M)`
(`kappa_subset_sigmaCompl`). -/
theorem kappa_subset_sigmaComplementPrimes [Finite G] {M : Subgroup G} :
    kappa M ⊆ sigmaComplementPrimes M := by
  intro p hpκ
  have hpsig : p ∈ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := kappa_subset_sigmaCompl hpκ
  obtain ⟨hpp, _, P, hPelem, hPM, _⟩ := hpκ
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩,
    hpsig⟩

/-- In a §12 `E`-setup, if the `σ(M)'`-complement `E` is a `κ(M)`-group (every prime divisor of
`|E|` lies in `κ(M)`), then `M` is type-`P₁`: `κ(M) = π(M) ∖ σ(M)`.  `E` is a `σ(M)'`-Hall, so it
carries every `σ(M)'`-prime of `M`; combined with `κ(M) ⊆ π(M) ∖ σ(M)` this forces equality.
Used to exclude the degenerate cases (`κ(M) ∩ τ₃(M) ≠ ∅`, or `E₂E₃ = 1`) when building the
matched `κ`-complement of a type-`P₂` maximal subgroup. -/
theorem kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (hEκ : ∀ p ∈ (Nat.card ↥E).primeFactors, p ∈ kappa M) :
    kappa M = sigmaComplementPrimes M := by
  refine le_antisymm kappa_subset_sigmaComplementPrimes (fun p hp => ?_)
  obtain ⟨hpπ, hpσ⟩ := hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpπ
  have hpM : p ∣ Nat.card ↥M := Nat.dvd_of_mem_primeFactors hpπ
  -- `p ∤ |M_σ|` (`M_σ` is a `σ(M)`-group and `p ∉ σ(M)`).
  have hpMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hd =>
    hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨hpp, hd, Nat.card_pos.ne'⟩))
  -- `p ∣ |E|` from `|M_σ| · |E| = |M|`.
  have hcardM := h.card_Msigma_mul_card_E
  have hpE : p ∣ Nat.card ↥E :=
    (hpp.dvd_mul.mp (hcardM ▸ hpM)).resolve_left hpMσ
  exact hEκ p (Nat.mem_primeFactors.mpr ⟨hpp, hpE, Nat.card_pos.ne'⟩)

/-- **`M`-conjugacy invariance of the `κ`-witness condition**: for `m ∈ M`, since `M_σ ◁ M`,
conjugation by `m` carries `M_σ ⊓ C_G(P)` to `M_σ ⊓ C_G(P^m)`, so `C_{M_σ}(P) ≠ 1` implies
`C_{M_σ}(P^m) ≠ 1`.  Used in Proposition 14.2 to transport the `κ(M)`-witness across
`M`-conjugacy (the `∃ → ∀` upgrade of BG L3807 and the WLOG `K = E₁`). -/
theorem Msigma_inf_centralizer_conj_ne_bot {M P : Subgroup G} {m : G} (hmM : m ∈ M)
    (h : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj m • P : Subgroup G) : Set G) ≠ ⊥ := by
  have hmN : m ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hmM
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  rw [Subgroup.mem_inf] at hxmem
  obtain ⟨hxMσ, hxC⟩ := hxmem
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨m * x * m⁻¹, Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hmN x).mp hxMσ, ?_⟩⟩, ?_⟩
  · -- `m x m⁻¹` centralizes `P^m`: write `y ∈ P^m` as `y = m (m⁻¹ y m) m⁻¹` with `m⁻¹ y m ∈ P`,
    -- which `x` centralizes.
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hyval : (MulAut.conj m)⁻¹ • y = m⁻¹ * y * m := by
      rw [inv_smul_eq_iff]
      show y = MulAut.conj m (m⁻¹ * y * m)
      rw [MulAut.conj_apply]; group
    rw [hyval] at hy
    have hcomm : (m⁻¹ * y * m) * x = x * (m⁻¹ * y * m) :=
      (Subgroup.mem_centralizer_iff.mp hxC) _ hy
    calc y * (m * x * m⁻¹)
        = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * x * m⁻¹) * y := by group
  · -- `m x m⁻¹ ≠ 1` since `x ≠ 1`.
    intro hc
    apply hx1
    have hxe : m * x * m⁻¹ = 1 := by simpa using congrArg Subtype.val hc
    refine Subtype.ext ?_
    have hconj : m * x * m⁻¹ = m * 1 * m⁻¹ := by rw [hxe]; group
    exact mul_left_cancel (mul_right_cancel hconj)

open OddOrder.BG.Ch3.S13 in
/-- In a §12 `E`-setup, a prime `p ∈ κ(M) ∩ τ₃(M)` forces `E₃ ≠ 1` and makes `E₃` act
non-regularly on `M_σ`: the `κ`-witness `P ∈ ℰ_p¹(M)` (with `C_{M_σ}(P) ≠ 1`) is `M`-conjugate
into the Hall `τ₃`-piece `E₃` (`exists_conj_smul_le_hallPiece`), and `M_σ`-centralizer
nontriviality transports along the conjugacy (`Msigma_inf_centralizer_conj_ne_bot`).  This is
the entry to BG Proposition 14.2's `κ ∩ τ₃ ≠ ∅` case (which then invokes Corollary 13.11). -/
theorem E3_not_regular_of_mem_kappa_tau3 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) (hpκ : p ∈ kappa M) (hpτ3 : p ∈ tau3 M) :
    E₃ ≠ ⊥ ∧ ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₃ := by
  obtain ⟨_, _, P, hPelem, hPM, hPC⟩ := hpκ
  haveI : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  have hPpi : Ch03.Subgroup.IsPiGroup (tau3 M) (P.subgroupOf M) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard,
      hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ3
  have hπσ : tau3 M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    fun q hq => ((mem_tau3_iff M q).mp hq).1
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG h h.E₃_le h.E₃_hall hπσ hPM hPpi
  have hPwC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≠ ⊥ :=
    Msigma_inf_centralizer_conj_ne_bot hwM hPC
  have hPwne : (MulAut.conj w • P : Subgroup G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one (conj_smul_mem_elemAbelianOfRank w hPelem)
  obtain ⟨⟨z, hzPw⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPwne
  have hz1' : z ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hzE3 : z ∈ E₃ := hwle hzPw
  refine ⟨fun hE3bot => hz1' (Subgroup.mem_bot.mp (hE3bot ▸ hzE3)), ?_⟩
  intro hreg
  have hzfix := hreg z hzE3 hz1'
  rw [fixedByElement] at hzfix
  apply hPwC
  rw [eq_bot_iff, ← hzfix]
  refine inf_le_inf_left _ ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact ha z hzPw

/-- **BG Proposition 14.2's `κ(M) ⊆ τ₁(M)` case entry** (mirror of `E3_not_regular_of_mem_kappa_tau3`):
a prime `p ∈ κ(M) ∩ τ₁(M)` forces `E₁ ≠ 1` and makes `E₁` act non-regularly on `M_σ` (the
`κ`-witness `P ∈ ℰ_p¹(M)` is `M`-conjugate into the Hall `τ₁`-piece `E₁`, transporting
`C_{M_σ}` nontriviality).  Feeds `κ(M) = τ₁(M)` and the `K^* ≠ 1` conjunct of case `τ₁`. -/
theorem E1_not_regular_of_mem_kappa_tau1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) (hpκ : p ∈ kappa M) (hpτ1 : p ∈ tau1 M) :
    E₁ ≠ ⊥ ∧ ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := by
  obtain ⟨_, _, P, hPelem, hPM, hPC⟩ := hpκ
  haveI : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  have hPpi : Ch03.Subgroup.IsPiGroup (tau1 M) (P.subgroupOf M) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard,
      hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ1
  have hπσ : tau1 M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    fun q hq => ((mem_tau1_iff M q).mp hq).1
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG h h.E₁_le h.E₁_hall hπσ hPM hPpi
  have hPwC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≠ ⊥ :=
    Msigma_inf_centralizer_conj_ne_bot hwM hPC
  have hPwne : (MulAut.conj w • P : Subgroup G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one (conj_smul_mem_elemAbelianOfRank w hPelem)
  obtain ⟨⟨z, hzPw⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPwne
  have hz1' : z ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hzE1 : z ∈ E₁ := hwle hzPw
  refine ⟨fun hE1bot => hz1' (Subgroup.mem_bot.mp (hE1bot ▸ hzE1)), ?_⟩
  intro hreg
  have hzfix := hreg z hzE1 hz1'
  rw [fixedByElement] at hzfix
  apply hPwC
  rw [eq_bot_iff, ← hzfix]
  refine inf_le_inf_left _ ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact ha z hzPw

/-- **Global `M_σ`-fixed point from prime action + a single non-regular point** (BG
Proposition 14.2, `κ(M) ∩ τ₃(M) ≠ ∅` case): if `E` acts in a prime manner on `M_σ` and some
`E₃ ≤ E` does not act regularly (a witness `x ∈ E₃#` has `C_{M_σ}(x) ≠ 1`), then prime action
collapses `C_{M_σ}(x) = C_{M_σ}(E)` for every `x ∈ E#`, so `C_{M_σ}(E) ≠ 1`.

Once `K = E` this is the conjunct `K^* = C_{M_σ}(K) ≠ 1`.  It also drives the `κ(M) ⊇ π(E)`
step of `K = E`: for each prime `p ∣ |E|`, a rank-one `P ≤ E` of order `p` has, by prime
action, `C_{M_σ}(P) = C_{M_σ}(E) ≠ 1`, so `p ∈ κ(M)`. -/
theorem Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular {M E E₃ : Subgroup G}
    (hEprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E) (hE3le : E₃ ≤ E)
    (hreg : ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₃) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
  -- A non-regular witness `x ∈ E₃#` with `C_{M_σ}(x) ≠ 1`.
  have hxex : ∃ x ∈ E₃, x ≠ 1 ∧
      fixedByElement (OddOrder.BG.Ch3.S10.Msigma M) x ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hreg fun x hx hx1 => hcon x hx hx1
  obtain ⟨x, hxE3, hx1, hxfix⟩ := hxex
  -- Prime action collapses the `x`-fixed points to the `E`-fixed points.
  have heq := hEprime x (hE3le hxE3) hx1
  rw [← fixedBy_def, ← heq]
  exact hxfix

/-- **Every prime dividing `|E|` lies in `τ₁(M) ∪ τ₃(M)`** in BG Proposition 14.2's
`κ(M) ∩ τ₃(M) ≠ ∅` case (the effective content of `E₂ = ⊥`): a prime `p ∣ |E|` is a
`σ(M)'`-prime with `r_p(M) ≤ 2`.  If `r_p(M) = 2` then `p ∈ τ₂(M)`, and Corollary 12.6
(`elemAb_normal_in_E_of_tau2`, projection on `E₃`) forces `C_{M_σ}(x) = 1` for the `E₃`-witness
`x`, contradicting `hxC`.  Hence `r_p(M) = 1`, so `p ∈ τ₁(M) ∪ τ₃(M)`.

Together with prime action (`C_{M_σ}(P) = C_{M_σ}(E) ≠ 1` for rank-one `P ≤ E`) this gives
`π(E) ⊆ κ(M)`, the key to `K = E` in the `κ ∩ τ₃` case. -/
theorem mem_tau1_union_tau3_of_mem_primeFactors_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∈ tau1 M ∪ tau3 M := by
  obtain ⟨hpp, hpdvdE, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hp
  have hr2 : pRank ↥M p ≤ 2 := h.pRank_M_le_two hG hp
  -- `p ∣ |M|`, so `r_p(M) ≥ 1`.
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hpp, hpdvdE.trans (Subgroup.card_dvd_of_le h.E_le), Nat.card_pos.ne'⟩
  have hr1 : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpM
  by_cases hr : pRank ↥M p = 2
  · -- `r_p(M) = 2 ⟹ p ∈ τ₂`, which makes `E₃` regular and kills the witness.
    exfalso
    have hpτ2 : p ∈ tau2 M := (mem_tau2_iff M p).mpr ⟨hpσ, hr⟩
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hpτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  · -- `r_p(M) = 1`: `p ∈ τ₃` if `p ∣ |M'|`, else `p ∈ τ₁`.
    have hr1' : pRank ↥M p = 1 := by omega
    by_cases hd : p ∈ tau3 M
    · exact Or.inr hd
    · refine Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, ?_, hr1'⟩)
      intro hderiv
      exact hd ((mem_tau3_iff M p).mpr ⟨hpσ, hderiv, hr1'⟩)

/-- **`π(E) ⊆ κ(M)`** in BG Proposition 14.2's `κ(M) ∩ τ₃(M) ≠ ∅` case: every prime `p ∣ |E|`
lies in `κ(M)`.  By `mem_tau1_union_tau3_of_mem_primeFactors_card_E`, `p ∈ τ₁(M) ∪ τ₃(M)`; and a
rank-one `P = ⟨g⟩ ≤ E` of order `p` (Cauchy) has `C_{M_σ}(P) = C_{M_σ}(g) = C_{M_σ}(E) ≠ 1` by
prime action (using the `E₃`-witness `x`), so `P` certifies `p ∈ κ(M)`.

This is the `K = E` step: with `π(E) ⊆ κ(M)` and the complement index `[M:E] = |M_σ|` coprime to
`κ(M)`, `E` is a Hall `κ(M)`-subgroup of `M`, hence equals the Hall `κ(M)`-subgroup `K ≤ E`. -/
theorem mem_kappa_of_mem_primeFactors_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hEprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E)
    {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∈ kappa M := by
  obtain ⟨hpp, hpdvdE, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hτ13 : p ∈ tau1 M ∪ tau3 M :=
    mem_tau1_union_tau3_of_mem_primeFactors_card_E hG h hxE3 hxne hxC hp
  -- `C_{M_σ}(E) ≠ 1` from the witness `x` and prime action.
  have hCE : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
    have heqx := hEprime x (h.E₃_le hxE3) hxne
    rw [← fixedBy_def, ← heqx]; exact hxC
  -- A rank-one `P = ⟨g⟩ ≤ E` of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvdE
  have hgE : (g : G) ∈ E := g.2
  have hgord : orderOf (g : G) = p :=
    (orderOf_injective E.subtype E.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by
    rw [Nat.card_zpowers]; exact hgord
  have hPelem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPM : Subgroup.zpowers (g : G) ≤ M := Subgroup.zpowers_le.mpr (h.E_le hgE)
  -- `C_{M_σ}(⟨g⟩) = C_{M_σ}(g) = C_{M_σ}(E) ≠ 1`.
  have heqg := hEprime (g : G) hgE hgne
  have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
  have hPC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) ≠ ⊥ := by
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ := by
      rw [← fixedByElement_def, heqg, fixedBy_def]; exact hCE
    exact fun hbot => hne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))
  exact ⟨hpp, hτ13, Subgroup.zpowers (g : G), hPelem, hPM, hPC⟩

/-- **`π(E₁) ⊆ κ(M)`** in BG Proposition 14.2's `κ(M) ⊆ τ₁(M)` case: every prime `p ∣ |E₁|` lies
in `κ(M)`.  `p ∈ τ₁(M)` (as `E₁` is Hall `τ₁(M)` of `E`), and a rank-one `P = ⟨g⟩ ≤ E₁` of order
`p` has `C_{M_σ}(P) = C_{M_σ}(E₁) ≠ 1` by prime action (`hE1prime`) plus `C_{M_σ}(E₁) ≠ 1`
(`hCE1`, from `E1_not_regular`).  So `E₁` is a `κ(M)`-subgroup; with `[M:E₁]` coprime to `κ(M)`
this makes `E₁` a Hall `κ(M)`-subgroup, conjugate to `K` (the entry to WLOG `K = E₁`). -/
theorem mem_kappa_of_mem_primeFactors_card_E1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁)
    (hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E₁).primeFactors) : p ∈ kappa M := by
  obtain ⟨hpp, hpdvdE1, -⟩ := Nat.mem_primeFactors.mp hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpτ1 : p ∈ tau1 M := h.E₁_hall.1 p (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv]; exact hp)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvdE1
  have hgE1 : (g : G) ∈ E₁ := g.2
  have hgord : orderOf (g : G) = p :=
    (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by
    rw [Nat.card_zpowers]; exact hgord
  have hPelem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPM : Subgroup.zpowers (g : G) ≤ M :=
    Subgroup.zpowers_le.mpr ((h.E₁_le.trans h.E_le) hgE1)
  have heqg := hE1prime (g : G) hgE1 hgne
  have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
  have hPC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) ≠ ⊥ := by
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ := by
      rw [← fixedByElement_def, heqg, fixedBy_def]; exact hCE1
    exact fun hbot => hne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))
  exact ⟨hpp, Or.inl hpτ1, Subgroup.zpowers (g : G), hPelem, hPM, hPC⟩

/-- **BG Proposition 14.2(c)** for the `κ(M) ∩ τ₃(M) ≠ ∅` case: if `X ∈ ℰ_q¹(G)` lies in
`K^* = C_{M_σ}(E)` (i.e. `X ≤ M_σ ⊓ C(E)`), then `𝓜(C_G(X)) = {M}`.  Here `q ∣ |M_σ|` forces
`q ∈ σ(M)`, and `X ≤ M_σ ⊓ C(E₁)` (since `E₁ ≤ E`), so Lemma 13.6
(`maximalContaining_eq_singleton_of_E1`) applies with `P = E₁` and a Sylow `q`-subgroup of `M_σ`.
With `K = E` this is the `𝓜(C_G(X)) = {M}` half of (c); it drives conjunct (d)
(`K^* ∩ M^g = 1` for `g ∉ M`). -/
theorem maximalContaining_centralizer_of_le_Msigma_centralizer_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    {X : Subgroup G} {q : ℕ} [Fact q.Prime] (hX : X ∈ elemAbelianOfRank G q 1)
    (hXK : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M := hXK.trans inf_le_left
  have hXcard : Nat.card ↥X = q := by rw [(mem_elemAbelianOfRank.mp hX).2, pow_one]
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  have hXC : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) :=
    le_inf hXMσ ((hXK.trans inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.E₁_le)))
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T →
      S = T := fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  exact (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hX hXC hSMσ hSq hSmax).1

/-- **BG Proposition 14.2(c)**, `C(E₁)` form (for case `κ ⊆ τ₁`, where `K^* = C_{M_σ}(K) = C_{M_σ}(E₁)`
after the WLOG `K = E₁`): if `X ∈ ℰ_q¹(G)` lies in `M_σ ⊓ C(E₁)`, then `𝓜(C_G(X)) = {M}`.  Same as
`maximalContaining_centralizer_of_le_Msigma_centralizer_E` but takes `X ≤ M_σ ⊓ C(E₁)` directly
(Lemma 13.6 with `P = E₁`). -/
theorem maximalContaining_centralizer_of_le_Msigma_centralizer_E1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    {X : Subgroup G} {q : ℕ} [Fact q.Prime] (hX : X ∈ elemAbelianOfRank G q 1)
    (hXC : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M := hXC.trans inf_le_left
  have hXcard : Nat.card ↥X = q := by rw [(mem_elemAbelianOfRank.mp hX).2, pow_one]
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T →
      S = T := fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  exact (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hX hXC hSMσ hSq hSmax).1

/-! ### Proposition 14.2(b1), case `κ(M) ⊆ τ₁(M)`: the Frobenius normalizer argument

In this case `K = E₁` (after the WLOG), and `E = E₁ ⋉ (E₂E₃)` is a Frobenius group: `E₁` acts
regularly (fixed-point-freely) on `U = E₂E₃` (BG mmd L3840, "by Lemma 13.12 and Lemma 13.7").
The regular action gives `N_E(X) ≤ E₁` for `X ∈ ℰ¹(E₁)`, which powers conjunct (b1). -/

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`, `E₃`-half** (mmd L3840, "by Lemma 13.7"): if `κ(M) ∩ τ₃(M)`
is empty (`κ ⊆ τ₁`) then `E₁` acts regularly on `E₃` (i.e. `C_{E₃}(g) = 1` for `g ∈ E₁#`).
Otherwise Lemma 13.7 makes `E₁E₃` act in a prime manner on `M_σ`, and since
`C_{M_σ}(E₁) = K^* ≠ 1`, prime action gives `C_{M_σ}(x) ≠ 1` for every `x ∈ E₃#`, producing a
prime of `κ(M) ∩ τ₃(M)` — a contradiction. -/
theorem actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) :
    ActsRegularlyOn E₃ E₁ := by
  classical
  by_contra hreg
  have hE3ne : E₃ ≠ ⊥ := fun hb => hreg (hb ▸ actsRegularlyOn_bot_left E₁)
  -- Lemma 13.7: `E₁E₃` acts in a prime manner on `M_σ`.
  have hprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) (E₁ ⊔ E₃) :=
    E1E3_actsPrime hG h hE1ne hreg
  -- `C_{M_σ}(E₁ ⊔ E₃) = C_{M_σ}(E₁) = K^* ≠ ⊥`.
  have hfix : fixedBy (OddOrder.BG.Ch3.S10.Msigma M) (E₁ ⊔ E₃)
      = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) :=
    (fixedBy_eq_of_le_of_ne_bot hprime le_sup_left hE1ne).symm
  -- A witness `x ∈ E₃#` then has `C_{M_σ}(x) = C_{M_σ}(E₁ ⊔ E₃) ≠ ⊥`.
  obtain ⟨⟨x, hxE3⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE3ne
  have hx1' : x ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    have hpx := hprime x (Subgroup.mem_sup_right hxE3) hx1'
    rw [fixedByElement_def] at hpx
    rw [hpx, hfix]; exact hKstar
  -- Build a `κ(M) ∩ τ₃(M)` witness: a rank-one `R ≤ ⟨x⟩ ≤ E₃` of prime order `r ∈ τ₃(M)`.
  refine hτ3 ?_
  have hxM : x ∈ M := h.E3_le_M hxE3
  have hxzpM : Subgroup.zpowers x ≤ E₃ := Subgroup.zpowers_le.mpr hxE3
  obtain ⟨r, hr, hrdvd⟩ :=
    (orderOf x).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) r
    (by rw [Nat.card_zpowers]; exact hrdvd)
  -- `R = ⟨z⟩`, with `z ∈ ⟨x⟩ ≤ E₃`, of order `r`.
  have hzx : (z : G) ∈ Subgroup.zpowers x := z.2
  have hRcard : Nat.card ↥(Subgroup.zpowers (z : G)) = r := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.zpowers x).subtype (Subgroup.zpowers x).subtype_injective z).trans hz
  have hRelem : Subgroup.zpowers (z : G) ∈ elemAbelianOfRank G r 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hRcard, by rw [hRcard, pow_one]⟩
  have hRE3 : Subgroup.zpowers (z : G) ≤ E₃ := (Subgroup.zpowers_le.mpr (hxzpM hzx))
  have hRM : Subgroup.zpowers (z : G) ≤ M := hRE3.trans (h.E3_le_M)
  -- `r ∈ τ₃(M)` (it divides `|E₃|`).
  have hrE3 : r ∈ (Nat.card ↥E₃).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hr, hRcard ▸ Subgroup.card_dvd_of_le hRE3, Nat.card_pos.ne'⟩
  have hrτ3 : r ∈ tau3 M := by
    have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    exact h.E₃_hall.1 r (hc3 ▸ hrE3)
  -- `C_{M_σ}(R) ⊇ C_{M_σ}(x) ≠ ⊥` (`z ∈ ⟨x⟩`, so centralizing `x` centralizes `⟨z⟩`).
  have hCle : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff] at ha ⊢
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hy
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzx
    have hxa : Commute x a := ha x rfl
    rw [← hm]
    exact ((hxa.zpow_left m).zpow_left j).eq
  have hRC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (z : G) : Subgroup G) : Set G) ≠ ⊥ :=
    fun hb => hxC (le_bot_iff.mp (hb ▸ inf_le_inf_left _ hCle))
  exact ⟨r, ⟨hr, Or.inr hrτ3, Subgroup.zpowers (z : G), hRelem, hRM, hRC⟩, hrτ3⟩

/-- `pRank` is preserved on passing to a subgroup of index coprime to `p` (the `p`-part of the
order is unchanged).  (Replicated here from the `private` copy in `S12_Corollary1216`.) -/
theorem pRank_eq_of_le_of_not_dvd_index [Finite G] {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hHK : H ≤ K) (hidx : ¬ p ∣ (H.subgroupOf K).index) :
    pRank ↥H p = pRank ↥K p := by
  obtain ⟨R⟩ : Nonempty (Sylow p ↥H) := inferInstance
  set Rincl : Subgroup ↥K := (R : Subgroup ↥H).map (Subgroup.inclusion hHK) with hRincl
  have hcardRincl : Nat.card ↥Rincl = p ^ (Nat.card ↥K).factorization p := by
    have hidxcard : Nat.card ↥H * (H.subgroupOf K).index = Nat.card ↥K := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
      exact (H.subgroupOf K).card_mul_index
    have hidx_ne : (H.subgroupOf K).index ≠ 0 := by
      intro hh; rw [hh, mul_zero] at hidxcard; exact (Nat.card_pos).ne' hidxcard.symm
    have hfact : (Nat.card ↥K).factorization p = (Nat.card ↥H).factorization p := by
      rw [← hidxcard, Nat.factorization_mul (Nat.card_pos).ne' hidx_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
    rw [hRincl, Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHK),
      R.card_eq_multiplicity, hfact]
  have eR : ↥(R : Subgroup ↥H) ≃* ↥Rincl :=
    hRincl ▸ Subgroup.equivMapOfInjective _ (Subgroup.inclusion hHK)
      (Subgroup.inclusion_injective hHK)
  have hSylK : pRank ↥Rincl p = pRank ↥K p := by
    have hh := pRank_sylow_eq (Sylow.ofCard Rincl hcardRincl)
    rwa [Sylow.coe_ofCard] at hh
  rw [← pRank_sylow_eq R, ← hSylK]
  exact le_antisymm (pRank_le_of_injective (f := eR.toMonoidHom) eR.injective)
    (pRank_le_of_injective (f := eR.symm.toMonoidHom) eR.symm.injective)

/-- For `q ∈ τ₂(M)` and a `q`-element `y' ∈ E₂#`, the `q`-torsion `Ω₁(E₂)` is a rank-two
elementary abelian `q`-subgroup of `E` containing `y'`.  (`E₂` is abelian by Corollary 12.10(b),
and `r_q(E₂) = r_q(E) = r_q(M) = 2` since the index steps `E₂ ≤ E ≤ M` are `q`-coprime.) -/
theorem exists_elemAb_rank_two_le_E_mem_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {y' : G} (hy'E2 : y' ∈ E₂) (hy'q : y' ^ q = 1) (hy'1 : y' ≠ 1) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ E ∧ y' ∈ A := by
  classical
  have hE2comm : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG h).2.1.1
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE2comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup G := omega1OfAbelian G E₂ q hcomm with hAdef
  have hAelem : A.IsElementaryAbelian q := omega1OfAbelian_isElementaryAbelian
  have hAE2 : A ≤ E₂ := omega1OfAbelian_le
  have hAE : A ≤ E := hAE2.trans h.E₂_le
  have hy'A : y' ∈ A := (mem_omega1OfAbelian).mpr ⟨hy'E2, hy'q⟩
  -- `r_q(E₂) = 2`: two `q`-coprime index steps `E₂ ≤ E ≤ M`, then `r_q(M) = 2`.
  have hpRankE2 : pRank ↥E₂ q = 2 := by
    have hr1 : pRank ↥E₂ q = pRank ↥E q :=
      pRank_eq_of_le_of_not_dvd_index h.E₂_le (fun hdvd =>
        h.E₂_hall.index_no_pi q (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq)
    have hr2 : pRank ↥E q = pRank ↥M q := by
      refine pRank_eq_of_le_of_not_dvd_index h.E_le (fun hdvd => ?_)
      have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hq
      have hidxeq : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h.isComplement'_subgroupOf.index_eq_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      rw [hidxeq] at hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rw [hr1, hr2, tau2_pRank_eq_two hq]
  -- `|A| = q²` from `q² ∣ |A|` (rank ≥ 2) and `log_q |A| ≤ r_q(E₂) = 2`.
  have hAcard : Nat.card ↥A = q ^ 2 := by
    have hdvd : q ^ 2 ∣ Nat.card ↥A :=
      hAdef ▸ pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankE2.ge
    have hlog_le : Nat.log q (Nat.card ↥A) ≤ 2 := by
      have hAsub : (A.subgroupOf E₂).IsElementaryAbelian q :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAE2).symm hAelem
      have hcardeq : Nat.card ↥(A.subgroupOf E₂) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE2).toEquiv
      have hle := le_pRank (A.subgroupOf E₂) hAsub
      rwa [hcardeq, hpRankE2] at hle
    have hcardpow : Nat.card ↥A = q ^ Nat.log q (Nat.card ↥A) := by
      rw [hAelem.log_card_eq_finrank, hAelem.card_eq_pow_finrank]
    have h2le : 2 ≤ Nat.log q (Nat.card ↥A) := by
      rw [hcardpow] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
    rw [hcardpow]; congr 1; omega
  exact ⟨A, ⟨hAelem, hAcard⟩, hAE, hy'A⟩

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`, `E₂`-half** (mmd L3840, "by Lemma 13.12"): if
`C_{M_σ}(E₁) = K^* ≠ 1` (i.e. `M` is type `P` in the `κ ⊆ τ₁` case) then `E₁` acts regularly on
`E₂`.  If some `g ∈ E₁#` centralized `y' ∈ E₂#` (of prime order `q ∈ τ₂(M)`), the rank-two
`A = Ω₁(E₂) ∋ y'` would give `C_A(⟨g₀⟩) ≠ 1`, so Lemma 13.12 forces `C_{M_σ}(⟨g₀⟩) = 1`,
contradicting `C_{M_σ}(⟨g₀⟩) = C_{M_σ}(E₁) = K^* ≠ 1` (prime action). -/
theorem actsRegularlyOn_E2_E1_of_actsPrime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥) :
    ActsRegularlyOn E₂ E₁ := by
  classical
  have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  intro g hgE1 hg1
  rw [fixedByElement_def]
  by_contra hne
  -- A witness `y ∈ E₂#` centralizing `g`.
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hyE2 : y ∈ E₂ := hy.1
  have hyCg : y ∈ Subgroup.centralizer ({g} : Set G) := hy.2
  have hy1' : y ≠ 1 := fun hc => hy1 (Subtype.ext hc)
  -- `g₀ ∈ ⟨g⟩` of prime order `p ∈ τ₁(M)`, `P = ⟨g₀⟩`.
  obtain ⟨p, hp, hpdvd⟩ :=
    (orderOf g).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers g)) p
    (by rw [Nat.card_zpowers]; exact hpdvd)
  have hg₀g : (g₀ : G) ∈ Subgroup.zpowers g := g₀.2
  have hgE1' : Subgroup.zpowers g ≤ E₁ := Subgroup.zpowers_le.mpr hgE1
  have hg₀E1 : (g₀ : G) ∈ E₁ := hgE1' hg₀g
  have hPcard : Nat.card ↥(Subgroup.zpowers (g₀ : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.zpowers g).subtype (Subgroup.zpowers g).subtype_injective g₀).trans hg₀
  have hPelem : Subgroup.zpowers (g₀ : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPbot : Subgroup.zpowers (g₀ : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hPelem
  have hPE1 : Subgroup.zpowers (g₀ : G) ≤ E₁ := Subgroup.zpowers_le.mpr hg₀E1
  have hPE : Subgroup.zpowers (g₀ : G) ≤ E := hPE1.trans h.E₁_le
  -- `p ∈ τ₁(M)`.
  have hpτ1 : p ∈ tau1 M := by
    have hc1 : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    refine h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩)
    exact hPcard ▸ Subgroup.card_dvd_of_le hPE1
  -- `C_{M_σ}(P) = C_{M_σ}(E₁) = K^* ≠ ⊥`.
  have hCP : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) ≠ ⊥ := by
    have := fixedBy_eq_of_le_of_ne_bot hE1prime hPE1 hPbot
    rw [fixedBy_def, fixedBy_def] at this
    rw [this]; exact hKstar
  -- `y' ∈ ⟨y⟩` of prime order `q ∈ τ₂(M)`.
  obtain ⟨q, hq, hqdvd⟩ :=
    (orderOf y).exists_prime_and_dvd (by rwa [Ne, orderOf_eq_one_iff])
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers y)) q
    (by rw [Nat.card_zpowers]; exact hqdvd)
  have hy'y : (y' : G) ∈ Subgroup.zpowers y := y'.2
  have hyE2' : Subgroup.zpowers y ≤ E₂ := Subgroup.zpowers_le.mpr hyE2
  have hy'E2 : (y' : G) ∈ E₂ := hyE2' hy'y
  have hy'ord : orderOf (y' : G) = q :=
    (orderOf_injective (Subgroup.zpowers y).subtype (Subgroup.zpowers y).subtype_injective y').trans hy'
  have hy'q : (y' : G) ^ q = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one _
  have hy'1 : (y' : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hy'ord; exact hq.ne_one hy'ord.symm
  -- `q ∈ τ₂(M)`.
  have hqτ2 : q ∈ tau2 M := by
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hy'zpE2 : Subgroup.zpowers (y' : G) ≤ E₂ := Subgroup.zpowers_le.mpr hy'E2
    have hqdvdE2 : q ∣ Nat.card ↥E₂ := by
      have h1 : Nat.card ↥(Subgroup.zpowers (y' : G)) = q := by rw [Nat.card_zpowers, hy'ord]
      exact h1 ▸ Subgroup.card_dvd_of_le hy'zpE2
    exact h.E₂_hall.1 q (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hq, hqdvdE2, Nat.card_pos.ne'⟩)
  -- rank-two `A = Ω₁(E₂) ∋ y'`.
  obtain ⟨A, hAmem, hAE, hy'A⟩ := exists_elemAb_rank_two_le_E_mem_of_tau2 hG h hqτ2 hy'E2 hy'q hy'1
  -- `y'` centralizes `g₀` (`y` centralizes `g`; `g₀ ∈ ⟨g⟩`, `y' ∈ ⟨y⟩`).
  have hComm_gy : Commute g y := hyCg g rfl
  have hy'Cg₀ : (y' : G) ∈ Subgroup.centralizer
      ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hw
    obtain ⟨i, rfl⟩ := hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg₀g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'y
    rw [← hj, ← hk]
    exact (((hComm_gy.zpow_left j).zpow_left i).zpow_right k).eq
  have hCAP : A ⊓ Subgroup.centralizer ((Subgroup.zpowers (g₀ : G) : Subgroup G) : Set G) ≠ ⊥ :=
    fun hb => hy'1 (Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_inf.mpr ⟨hy'A, hy'Cg₀⟩))
  -- Lemma 13.12: `C_{M_σ}(P) = ⊥`, contradicting `C_{M_σ}(P) = K^* ≠ ⊥`.
  exact hCP (Msigma_centralizer_eq_bot_of_tau1_tau2 hG h hpτ1 hqτ2 hPelem hPE hAmem hAE hCAP)

/-- **BG Prop 14.2(a), case `κ ⊆ τ₁`: `E₁` acts regularly on `U = E₂E₃`** (mmd L3840,
"acts regularly on `U = E₂E₃`").  Combines the `E₃`- and `E₂`-halves: `E = E₁ ⋉ (E₂E₃)` with
`E₃ ⊴ E` (Lemma 12.1(b)) and `E₁` normalizing `E₂` (Lemma 12.1(e)), so for `g ∈ E₁#` a fixed
`u = u₃u₂ ∈ E₂E₃` has both factors fixed (`E₂ ⊓ E₃ = 1`), forcing `u = 1`. -/
theorem actsRegularlyOn_E23_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) :
    ActsRegularlyOn (E₂ ⊔ E₃) E₁ := by
  classical
  have hregE3 : ActsRegularlyOn E₃ E₁ :=
    actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty hG h hE1ne hKstar hτ3
  have hregE2 : ActsRegularlyOn E₂ E₁ :=
    actsRegularlyOn_E2_E1_of_actsPrime hG h hE1ne hKstar
  have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG h).2.1.2
  have hE12normE2 : E₁ ⊔ E₂ ≤ Subgroup.normalizer (E₂ : Set G) :=
    (subgroupE_basic hG h).2.2.2.2.1.2.2
  -- `E₂ ⊓ E₃ = ⊥` (coprime: `τ₂ ∩ τ₃ = ∅`).
  have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    have hsτ2 : s ∈ tau2 M := h.E₂_hall.1 s (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩)
    have hsτ3 : s ∈ tau3 M := h.E₃_hall.1 s (hc3 ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩)
    have h2 := tau2_pRank_eq_two hsτ2
    have h1 := tau3_pRank_eq_one hsτ3
    omega
  have hE23disj : E₂ ⊓ E₃ = ⊥ := by
    have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
    have hc1 : Nat.card ↥(E₂ ⊓ E₃) = 1 := Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2)
    exact Subgroup.card_eq_one.mp hc1
  haveI hE3normSub : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr hEnormE3
  intro g hgE1 hg1
  rw [fixedByElement_def]
  have hgNE2 : g ∈ Subgroup.normalizer (E₂ : Set G) := hE12normE2 (Subgroup.mem_sup_left hgE1)
  have hgNE3 : g ∈ Subgroup.normalizer (E₃ : Set G) := hEnormE3 (h.E₁_le hgE1)
  refine le_antisymm ?_ bot_le
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨huU, huCg⟩ := hu
  -- `gug⁻¹ = u`.
  have hgu : g * u = u * g := huCg g rfl
  -- decompose `u = u₃ * u₂` in `↥E` (`E₃` normal).
  have huE : u ∈ E := (sup_le h.E₂_le h.E₃_le) huU
  have hsupSub : (E₂ ⊔ E₃).subgroupOf E = E₃.subgroupOf E ⊔ E₂.subgroupOf E := by
    rw [Subgroup.subgroupOf_sup h.E₂_le h.E₃_le, sup_comm]
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsupSub ▸ Subgroup.mem_subgroupOf.mpr huU :
      (⟨u, huE⟩ : ↥E) ∈ E₃.subgroupOf E ⊔ E₂.subgroupOf E)
  have hu3 : (a : G) ∈ E₃ := Subgroup.mem_subgroupOf.mp ha
  have hu2 : (b : G) ∈ E₂ := Subgroup.mem_subgroupOf.mp hb
  have hu32 : (a : G) * (b : G) = u := by have hh := congrArg Subtype.val hab; simpa using hh
  -- `g·u₃·g⁻¹ ∈ E₃`, `g·u₂·g⁻¹ ∈ E₂`.
  have hw3 : g * (a : G) * g⁻¹ ∈ E₃ := (Subgroup.mem_normalizer_iff.mp hgNE3 (a : G)).mp hu3
  have hw2 : g * (b : G) * g⁻¹ ∈ E₂ := (Subgroup.mem_normalizer_iff.mp hgNE2 (b : G)).mp hu2
  -- `(g u₃ g⁻¹)(g u₂ g⁻¹) = u₃ u₂`.
  have hconj : (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹) = (a : G) * (b : G) := by
    have hgug : g * u * g⁻¹ = u := by rw [hgu]; group
    calc (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        = g * ((a : G) * (b : G)) * g⁻¹ := by group
      _ = g * u * g⁻¹ := by rw [hu32]
      _ = u := hgug
      _ = (a : G) * (b : G) := hu32.symm
  -- `c := u₃⁻¹·(g u₃ g⁻¹) = u₂·(g u₂ g⁻¹)⁻¹ ∈ E₂ ⊓ E₃ = 1`.
  set c : G := (a : G)⁻¹ * (g * (a : G) * g⁻¹) with hcdef
  have hcE3 : c ∈ E₃ := E₃.mul_mem (E₃.inv_mem hu3) hw3
  have hcE2 : c = (b : G) * (g * (b : G) * g⁻¹)⁻¹ := by
    have hw3eq : g * (a : G) * g⁻¹ = (a : G) * (b : G) * (g * (b : G) * g⁻¹)⁻¹ := by
      rw [← hconj]; group
    rw [hcdef, hw3eq]; group
  have hcE2' : c ∈ E₂ := hcE2 ▸ E₂.mul_mem hu2 (E₂.inv_mem hw2)
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hE23disj ▸ Subgroup.mem_inf.mpr ⟨hcE2', hcE3⟩)
  -- so `g u₃ g⁻¹ = u₃` and (symmetrically) `g u₂ g⁻¹ = u₂`; both centralized ⟹ in `E_i ⊓ C(g) = ⊥`.
  have hu3fix : g * (a : G) * g⁻¹ = (a : G) := (inv_mul_eq_one.mp (hcdef ▸ hc1)).symm
  have hw2fix : g * (b : G) * g⁻¹ = (b : G) :=
    (mul_inv_eq_one.mp (by rw [← hcE2]; exact hc1)).symm
  have hu3bot : (a : G) = 1 := by
    have hmem : (a : G) ∈ E₃ ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu3, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (mul_inv_eq_iff_eq_mul.mp hu3fix)
    have hr := hregE3 g hgE1 hg1
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  have hu2bot : (b : G) = 1 := by
    have hmem : (b : G) ∈ E₂ ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (mul_inv_eq_iff_eq_mul.mp hw2fix)
    have hr := hregE2 g hgE1 hg1
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  rw [Subgroup.mem_bot, ← hu32, hu3bot, hu2bot, mul_one]

/-- **BG Prop 14.2(b1), case `κ ⊆ τ₁`: `N_E(X) ≤ E₁`** for `X ∈ ℰ¹(E₁)` (the Frobenius
normalizer fact).  Writing `e = u·k` (`u ∈ E₂E₃`, `k ∈ E₁`), `E₁` abelian gives `kgk⁻¹ = g`, so
`ugu⁻¹ = ege⁻¹ ∈ X ≤ E₁`; then `[u,g] ∈ E₁ ⊓ E₂E₃ = 1`, so `u` centralizes `g` and lies in
`C_{E₂E₃}(g) = 1` (regular action), forcing `u = 1`, i.e. `e = k ∈ E₁`. -/
theorem normalizer_inf_E_le_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    {X : Subgroup G} {p : ℕ} [Fact p.Prime] (hX : X ∈ elemAbelianOfRank G p 1)
    (hXE1 : X ≤ E₁) :
    Subgroup.normalizer (X : Set G) ⊓ E ≤ E₁ := by
  classical
  have hreg23 : ActsRegularlyOn (E₂ ⊔ E₃) E₁ :=
    actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3
  have hE1cyc : IsCyclic ↥E₁ := (subgroupE_basic hG h).2.2.2.1.1
  have hEnormE3 : E ≤ Subgroup.normalizer (E₃ : Set G) := (subgroupE_basic hG h).2.1.2
  have hE23norm : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) :=
    (subgroupE_basic hG h).2.2.2.2.1.2.1
  have hEsup : E = E₁ ⊔ E₂ ⊔ E₃ := (subgroupE_basic hG h).2.2.2.2.1.1
  letI : CommGroup ↥E₁ := hE1cyc.commGroup
  -- generator `g` of `X`.
  obtain ⟨⟨g, hgX⟩, hg1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hX)
  have hg1' : g ≠ 1 := fun hc => hg1 (Subtype.ext hc)
  have hgE1 : g ∈ E₁ := hXE1 hgX
  -- `E₁ ⊓ (E₂⊔E₃) = ⊥` (coprime `τ₁` vs `τ₂ ∪ τ₃`).
  have hc1E : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
  have hc2E : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
  have hc3E : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
  have hcop2 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₂) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have := tau1_pRank_eq_one (h.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
    have := tau2_pRank_eq_two (h.E₂_hall.1 s (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
    omega
  have hcop3 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact not_mem_tau3_of_mem_tau1
      (h.E₁_hall.1 s (hc1E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      (h.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
  have hE23disj : E₂ ⊓ E₃ = ⊥ := by
    have hd1 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₂ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₂ ⊓ E₃) ∣ Nat.card ↥E₃ := Subgroup.card_dvd_of_le inf_le_right
    have hcop23 : Nat.Coprime (Nat.card ↥E₂) (Nat.card ↥E₃) := by
      by_contra hnc
      obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      have := tau2_pRank_eq_two (h.E₂_hall.1 s (hc2E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsm, Nat.card_pos.ne'⟩))
      have := tau3_pRank_eq_one (h.E₃_hall.1 s (hc3E ▸ Nat.mem_primeFactors.mpr ⟨hs, hsn, Nat.card_pos.ne'⟩))
      omega
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop23 ▸ Nat.dvd_gcd hd1 hd2))
  have hcard23 : Nat.card ↥(E₂ ⊔ E₃) = Nat.card ↥E₂ * Nat.card ↥E₃ :=
    card_sup_eq_mul_of_le_normalizer_of_disjoint (h.E₂_le.trans hEnormE3) hE23disj
  have hE1_23_disj : E₁ ⊓ (E₂ ⊔ E₃) = ⊥ := by
    have hd1 : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ∣ Nat.card ↥E₁ := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ∣ Nat.card ↥(E₂ ⊔ E₃) := Subgroup.card_dvd_of_le inf_le_right
    have hcop : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(E₂ ⊔ E₃)) :=
      hcard23 ▸ Nat.Coprime.mul_right hcop2 hcop3
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2))
  -- the normalizer membership.
  intro e he
  rw [Subgroup.mem_inf] at he
  obtain ⟨heN, heE⟩ := he
  -- decompose `e = u * k`, `u ∈ E₂⊔E₃` (normal), `k ∈ E₁`.
  haveI hUnorm : ((E₂ ⊔ E₃).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le h.E₂_le h.E₃_le)).mpr hE23norm
  have hsuptop : ((E₂ ⊔ E₃).subgroupOf E) ⊔ (E₁.subgroupOf E) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (sup_le h.E₂_le h.E₃_le) h.E₁_le, Subgroup.subgroupOf_eq_top,
      hEsup]
    exact sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  obtain ⟨u, hu, k, hk, huk⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsuptop ▸ Subgroup.mem_top (⟨e, heE⟩ : ↥E))
  have huU : (u : G) ∈ E₂ ⊔ E₃ := Subgroup.mem_subgroupOf.mp hu
  have hkE1 : (k : G) ∈ E₁ := Subgroup.mem_subgroupOf.mp hk
  have huke : (u : G) * (k : G) = e := by have hh := congrArg Subtype.val huk; simpa using hh
  -- `k` commutes with `g` (`E₁` abelian).
  have hkg : (k : G) * g = g * (k : G) :=
    congrArg Subtype.val (mul_comm (⟨(k : G), hkE1⟩ : ↥E₁) (⟨g, hgE1⟩ : ↥E₁))
  -- `e g e⁻¹ = u g u⁻¹ ∈ X ≤ E₁`.
  have hege : e * g * e⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp heN g).mp hgX
  have hugu : (u : G) * g * (u : G)⁻¹ = e * g * e⁻¹ := by
    have hkgk : (k : G) * g * (k : G)⁻¹ = g := by rw [hkg]; group
    rw [← huke]
    calc (u : G) * g * (u : G)⁻¹
        = (u : G) * ((k : G) * g * (k : G)⁻¹) * (u : G)⁻¹ := by rw [hkgk]
      _ = (u : G) * (k : G) * g * ((u : G) * (k : G))⁻¹ := by group
  have huguE1 : (u : G) * g * (u : G)⁻¹ ∈ E₁ := hXE1 (hugu ▸ hege)
  -- `[u,g] ∈ E₁ ⊓ (E₂⊔E₃) = ⊥`.
  have hcommE1 : (u : G) * g * (u : G)⁻¹ * g⁻¹ ∈ E₁ := E₁.mul_mem huguE1 (E₁.inv_mem hgE1)
  have hgU : g ∈ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := hE23norm (h.E₁_le hgE1)
  have hcommU : (u : G) * g * (u : G)⁻¹ * g⁻¹ ∈ E₂ ⊔ E₃ := by
    have h1 : g * (u : G)⁻¹ * g⁻¹ ∈ E₂ ⊔ E₃ :=
      (Subgroup.mem_normalizer_iff.mp hgU (u : G)⁻¹).mp ((E₂ ⊔ E₃).inv_mem huU)
    have heq : (u : G) * g * (u : G)⁻¹ * g⁻¹ = (u : G) * (g * (u : G)⁻¹ * g⁻¹) := by group
    rw [heq]; exact (E₂ ⊔ E₃).mul_mem huU h1
  have hcomm1 : (u : G) * g * (u : G)⁻¹ * g⁻¹ = 1 :=
    Subgroup.mem_bot.mp (hE1_23_disj ▸ Subgroup.mem_inf.mpr ⟨hcommE1, hcommU⟩)
  -- `u ∈ C_{E₂⊔E₃}(g) = ⊥`, so `u = 1` and `e = k ∈ E₁`.
  have hu1 : (u : G) = 1 := by
    have hug : (u : G) * g = g * (u : G) :=
      mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm1)
    have hmem : (u : G) ∈ (E₂ ⊔ E₃) ⊓ Subgroup.centralizer ({g} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨huU, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact hug.symm
    have hr := hreg23 g hgE1 hg1'
    rw [fixedByElement_def] at hr
    exact Subgroup.mem_bot.mp (hr ▸ hmem)
  rw [← huke, hu1, one_mul]; exact hkE1

/-- **The §12 complement `E` is a Frobenius group** in case `τ₁` with `U = E₂E₃ ≠ 1`.
`E₁` acts regularly (fixed-point-freely) on the normal subgroup `U = E₂ ⊔ E₃`
(`actsRegularlyOn_E23_E1_of_caseTau1`), and `E = E₁ ⋉ U` (`SubgroupESetup.eq_sup`), so `E` is a
Frobenius group with kernel `U` and complement `E₁`.  This is the Frobenius structure that
Proposition 14.2(g) feeds to Theorem 3.10(a). -/
theorem isFrobeniusGroup_E_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥E
      ((E₂ ⊔ E₃).subgroupOf E) (E₁.subgroupOf E) := by
  classical
  have hreg : ActsRegularlyOn (E₂ ⊔ E₃) E₁ :=
    actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3
  have hE23le : (E₂ ⊔ E₃ : Subgroup G) ≤ E := sup_le h.E₂_le h.E₃_le
  have hE1le : E₁ ≤ E := h.E₁_le
  have hE23norm : E ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := h.E23_normal hG
  -- `E₁ ⊓ (E₂ ⊔ E₃) = ⊥` (a nonidentity common element would centralize itself, contra FPF).
  have hdisj : E₁ ⊓ (E₂ ⊔ E₃) = ⊥ := by
    refine le_antisymm (fun g hg => ?_) bot_le
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE1, hgU⟩ := hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hr := hreg g hgE1 hg1
    rw [fixedByElement_def, eq_bot_iff] at hr
    refine hg1 (Subgroup.mem_bot.mp (hr ?_))
    exact Subgroup.mem_inf.mpr ⟨hgU, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy])⟩
  -- normality of the kernel.
  haveI hKnorm : ((E₂ ⊔ E₃).subgroupOf E).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hE23norm
  refine ⟨hKnorm, ?_, ?_, ?_, ?_⟩
  · -- complement: disjoint + product covers `↥E`.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      have hi : (E₂ ⊔ E₃).subgroupOf E ⊓ E₁.subgroupOf E = ((E₂ ⊔ E₃) ⊓ E₁).subgroupOf E := rfl
      rw [hi, inf_comm, hdisj, Subgroup.bot_subgroupOf]
    · haveI := hKnorm
      have hsupG : (E₂ ⊔ E₃) ⊔ E₁ = E := by rw [h.eq_sup hG]; ac_rfl
      have hsup : (E₂ ⊔ E₃).subgroupOf E ⊔ E₁.subgroupOf E = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hE23le hE1le, hsupG, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul ((E₂ ⊔ E₃).subgroupOf E) (E₁.subgroupOf E)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hUne (hd.eq_bot_of_le hE23le)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hE1ne (hd.eq_bot_of_le hE1le)
  · -- Frobenius condition from the fixed-point-free action.
    intro a ha hane n hn hnne
    simp only [Subgroup.mem_subgroupOf] at ha hn
    intro hcontra
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := congrArg (Subtype.val) hcontra; push_cast at this; exact this
    have hane' : (a : G) ≠ 1 := fun hc => hane (Subtype.ext (by simpa using hc))
    have hnne' : (n : G) ≠ 1 := fun hc => hnne (Subtype.ext (by simpa using hc))
    have hr := hreg (a : G) ha hane'
    rw [fixedByElement_def, eq_bot_iff] at hr
    refine hnne' (Subgroup.mem_bot.mp (hr ?_))
    exact Subgroup.mem_inf.mpr ⟨hn, Subgroup.mem_centralizer_iff.mpr
      (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact mul_inv_eq_iff_eq_mul.mp hval)⟩

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
  simp only [maximalTypeFFamily, maximalTypePFamily, Set.mem_setOf_eq, Set.mem_sdiff, not_and]
  constructor
  · rintro ⟨hM, hF⟩
    exact ⟨hM, fun _ => isTypeF_iff_not_isTypeP.mp hF⟩
  · rintro ⟨hM, hnP⟩
    exact ⟨hM, isTypeF_iff_not_isTypeP.mpr (hnP hM)⟩

/-- BG `M_sigma(x)`: maximal subgroups whose `M_sigma` contains the element `x`. -/
def maximalSigmaSubgroupsOfElement (x : G) : Set (Subgroup G) :=
  {M | M ∈ maximalSubgroups G ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma M}

/-- The nonidentity part `M_σ^#` of `M_σ` (`= sharpSubgroup M_σ`).

**Naming caveat (2026-06-14):** BG's `M̃` — used in Lemma 14.5(c), Theorem 14.7(e), and the
Corollary 14.9 covering — is the *larger* set `{ x x' | x ∈ M_σ^#, x' ∈ R(x) }`, where `R(x)`
is the normal Hall subgroup of `C_G(x)` from Theorem 14.4 (it adjoins the `ℓ_σ = 2` "twisted"
elements). `R(x)` and hence `M̃` are **not yet formalized** (gated on Theorem 14.4 ⟸ §13), so
this `sigmaSharp` is only the `ℓ_σ = 1` core `M_σ^#`, a strict under-approximation of `M̃`.
Any downstream use (§15/§16, Corollary 14.9) that intends BG's `M̃` must switch to the
eventual `M̃` once `R(x)` is available. See `notes/bg/s14_typeP_counting.md`. -/
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

/-- A conjugate of a maximal subgroup is maximal: `IsConjugateSubgroup` preserves
`maximalSubgroups`.  The type-`P` conjugacy arguments of Theorem 14.7 and Corollary 14.8 move
maximal subgroups around by conjugation, so they need maximality to be conjugacy-stable. -/
theorem mem_maximalSubgroups_of_isConjugateSubgroup {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h : IsConjugateSubgroup M N) :
    N ∈ maximalSubgroups G := by
  obtain ⟨g, rfl⟩ := h
  exact mem_maximalSubgroups.mpr
    (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hM))

/-- `Z_tilde = Z - (K union K*)` in Theorem 14.7. -/
def zTilde (K Kstar : Subgroup G) : Set G :=
  ((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G))

/-! ### Genuine `σ`-decomposition of an element (BG §14 opening, Coq `sigma_decomposition`)

Built on the two-block π-part decomposition `OddOrder.GroupTheory.exists_isPiElement_mul`.  These
genuine definitions (`sigmaPart`, `sigmaDecomposition`, `sigmaLength`) construct the carrier that
`SigmaDecompositionData` below only *posits*: `sigmaLength` is an honest `ℕ`-valued function with
`sigmaLength_eq_zero_iff` (Coq `ell_sigma0P`) and `sigmaLength_conj` (conjugation invariance,
Coq `ell_sigmaJ`) proven from the construction, not a free structure field.  This is the upstream
foundation of the `FT_signalizer` (Theorem D(3)/(4)) port (issue 8020, Chunk 1). -/

/-- The `π`-part of a finite-order element `g`, as a *function*: the `π`-element factor of the
unique two-block decomposition `g = (π-part) * (π′-part)` (`exists_isPiElement_mul`, made into a
function via `Classical.choose`).  This is Coq's `g.`_π`. -/
noncomputable def piPart [Finite G] (π : Set ℕ) (g : G) : G :=
  (exists_isPiElement_mul π g).choose

/-- The decomposition behind `piPart`: there is a commuting `π′`-element `b`, a power of `g`, with
`piPart π g * b = g`. -/
theorem piPart_spec [Finite G] (π : Set ℕ) (g : G) :
    ∃ b : G, piPart π g * b = g ∧ Commute (piPart π g) b ∧
      IsPiElement π (piPart π g) ∧ IsPiElement πᶜ b ∧
      piPart π g ∈ Subgroup.zpowers g ∧ b ∈ Subgroup.zpowers g :=
  (exists_isPiElement_mul π g).choose_spec

/-- `piPart π g` is a `π`-element. -/
theorem isPiElement_piPart [Finite G] (π : Set ℕ) (g : G) : IsPiElement π (piPart π g) := by
  obtain ⟨_, _, _, h, _, _, _⟩ := piPart_spec π g; exact h

/-- The identity has trivial `π`-part. -/
theorem piPart_one [Finite G] (π : Set ℕ) : piPart π (1 : G) = 1 := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π (1 : G)
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (one_mul (1 : G)) (Commute.refl 1)
    (isPiElement_one π) (isPiElement_one πᶜ)).1

/-- If the `π`-part of `g` is trivial, then `g` itself is a `π′`-element. -/
theorem isPiElement_compl_of_piPart_eq_one [Finite G] {π : Set ℕ} {g : G}
    (h : piPart π g = 1) : IsPiElement πᶜ g := by
  obtain ⟨b, hmul, -, -, hpiB, -, -⟩ := piPart_spec π g
  rw [h, one_mul] at hmul
  rwa [hmul] at hpiB

/-- Conjugation preserves the `π`-element property (the conjugate has the same order). -/
theorem isPiElement_conj {π : Set ℕ} (h : G) {a : G} (ha : IsPiElement π a) :
    IsPiElement π (h * a * h⁻¹) := by
  have key : orderOf (h * a * h⁻¹) = orderOf a := by
    have hh := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective a
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hh
  intro p hp
  rw [key] at hp
  exact ha p hp

/-- **The `π`-part is conjugation-equivariant** (`piPart π (h x h⁻¹) = h (piPart π x) h⁻¹`).
Conjugating the unique decomposition `x = (π-part)(π′-part)` gives a decomposition of `h x h⁻¹`;
uniqueness identifies its `π`-part with `h (piPart π x) h⁻¹`. -/
theorem piPart_conj [Finite G] (π : Set ℕ) (h x : G) :
    piPart π (h * x * h⁻¹) = h * piPart π x * h⁻¹ := by
  obtain ⟨bx, hxmul, hxcomm, hxpiA, hxpiB, -, -⟩ := piPart_spec π x
  obtain ⟨b', hmul', hcomm', hpiA', hpiB', -, -⟩ := piPart_spec π (h * x * h⁻¹)
  have hprod : (h * piPart π x * h⁻¹) * (h * bx * h⁻¹) = h * x * h⁻¹ := by
    calc (h * piPart π x * h⁻¹) * (h * bx * h⁻¹)
        = h * (piPart π x * bx) * h⁻¹ := by group
      _ = h * x * h⁻¹ := by rw [hxmul]
  have hBcomm : Commute (h * piPart π x * h⁻¹) (h * bx * h⁻¹) := by
    have hm := hxcomm.map (MulAut.conj h)
    simpa only [MulAut.conj_apply] using hm
  exact (isPiElement_mul_unique hmul' hcomm' hpiA' hpiB' hprod hBcomm
    (isPiElement_conj h hxpiA) (isPiElement_conj h hxpiB)).1

/-- A `π`-element is its own `π`-part. -/
theorem piPart_self_of_isPiElement [Finite G] {π : Set ℕ} {g : G} (hg : IsPiElement π g) :
    piPart π g = g := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π g
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (mul_one g) (Commute.one_right g)
    hg (isPiElement_one πᶜ)).1

/-- A `π′`-element has trivial `π`-part. -/
theorem piPart_eq_one_of_isPiElement_compl [Finite G] {π : Set ℕ} {g : G}
    (hg : IsPiElement πᶜ g) : piPart π g = 1 := by
  obtain ⟨b, hmul, hcomm, hpiA, hpiB, -, -⟩ := piPart_spec π g
  exact (isPiElement_mul_unique hmul hcomm hpiA hpiB (one_mul g) (Commute.one_left g)
    (isPiElement_one π) hg).1

/-- The `π`-part of `g` is a power of `g`. -/
theorem piPart_mem_zpowers [Finite G] (π : Set ℕ) (g : G) :
    piPart π g ∈ Subgroup.zpowers g := by
  obtain ⟨_, _, _, _, _, hz, _⟩ := piPart_spec π g; exact hz

/-- A prime of `π` dividing `orderOf g` also divides `orderOf (piPart π g)` (it cannot land in the
`π′`-part `b`, whose order is coprime to `π`). -/
theorem prime_dvd_orderOf_piPart [Finite G] {π : Set ℕ} {p : ℕ} (hp : p.Prime) (hpπ : p ∈ π)
    {g : G} (hpg : p ∣ orderOf g) : p ∣ orderOf (piPart π g) := by
  obtain ⟨b, hmul, hcomm, _, hpiB, _, _⟩ := piPart_spec π g
  have hdvd : orderOf g ∣ orderOf (piPart π g) * orderOf b := by
    have h := hcomm.orderOf_mul_dvd_mul_orderOf; rwa [hmul] at h
  rcases hp.dvd_mul.mp (hpg.trans hdvd) with h | h
  · exact h
  · exact absurd hpπ (hpiB p (Nat.mem_primeFactors.mpr ⟨hp, h, (orderOf_pos b).ne'⟩))

/-- **The `π`-part is multiplicative on commuting elements** (Coq `consttM`): for commuting `x, y`,
`piPart π (x * y) = piPart π x * piPart π y`.  Both `π`-parts are powers of `x`, `y`, so they commute
(as do the two `π′`-parts and the cross pairs), letting `x * y = (xπ yπ)(xπ′ yπ′)` be rearranged into
a commuting `π`-element times `π′`-element; uniqueness of the `π`-decomposition
(`isPiElement_mul_unique`) identifies its `π`-part with `xπ yπ`.  The computational tool behind the
`σ`-decomposition of a `σ`-cover element `x · R(x)` (BG Lemma 14.5). -/
theorem piPart_mul_of_commute [Finite G] {π : Set ℕ} {x y : G} (hcomm : Commute x y) :
    piPart π (x * y) = piPart π x * piPart π y := by
  obtain ⟨cx, hxmul, hxc, hxπ, hxπ', hxz, hcxz⟩ := piPart_spec π x
  obtain ⟨cy, hymul, hyc, hyπ, hyπ', hyz, hcyz⟩ := piPart_spec π y
  obtain ⟨c, hmul, hc, hπ, hπ', -, -⟩ := piPart_spec π (x * y)
  -- powers of `x` commute with powers of `y` (as `x, y` commute).
  have hcross : ∀ {a b : G}, a ∈ Subgroup.zpowers x → b ∈ Subgroup.zpowers y → Commute a b := by
    intro a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hcomm.zpow_zpow m n
  have hcyx : Commute (piPart π y) cx := (hcross hcxz hyz).symm
  have hprod : (piPart π x * piPart π y) * (cx * cy) = x * y := by
    calc (piPart π x * piPart π y) * (cx * cy)
        = piPart π x * (piPart π y * cx) * cy := by group
      _ = piPart π x * (cx * piPart π y) * cy := by rw [hcyx]
      _ = (piPart π x * cx) * (piPart π y * cy) := by group
      _ = x * y := by rw [hxmul, hymul]
  have hABcomm : Commute (piPart π x * piPart π y) (cx * cy) :=
    Commute.mul_left (Commute.mul_right hxc (hcross hxz hcyz))
      (Commute.mul_right (hcross hcxz hyz).symm hyc)
  exact (isPiElement_mul_unique hmul hc hπ hπ' hprod hABcomm
    (isPiElement_mul_of_commute (hcross hxz hyz) hxπ hyπ)
    (isPiElement_mul_of_commute (hcross hcxz hcyz) hxπ' hyπ')).1

/-- The `σ(M)`-part of an element `x` (Coq `x.`_{σ(M)}`): its `σ(M)`-component in the two-block
π-part decomposition. -/
noncomputable def sigmaPart [Finite G] (M : Subgroup G) (x : G) : G :=
  piPart (OddOrder.BG.Ch3.S10.sigma M) x

/-- The `σ(M)`-part is conjugation-equivariant. -/
theorem sigmaPart_conj [Finite G] (M : Subgroup G) (h x : G) :
    sigmaPart M (h * x * h⁻¹) = h * sigmaPart M x * h⁻¹ := by
  simp only [sigmaPart]; exact piPart_conj _ h x

/-- **BG `sigma_decomposition x`** (Coq `sigma_decomposition`): the set of nonidentity `σ(M)`-parts
of `x` ranging over the maximal subgroups `M`. -/
noncomputable def sigmaDecomposition [Finite G] (x : G) : Set G :=
  {y | ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ y = sigmaPart M x} \ {1}

/-- **BG `sigma_length x = #|sigma_decomposition x|`** (Coq `sigma_length`).  `sigmaLength_eq_zero_iff`
(Coq `ell_sigma0P`) is proved further down, after `exists_mem_sigma_of_prime_dvd_card`. -/
noncomputable def sigmaLength [Finite G] (x : G) : ℕ :=
  (sigmaDecomposition x).ncard

/-- **BG `ell_sigmaJ`**: the σ-length is conjugation-invariant.  Conjugation by `h` is a bijection
of `G` carrying `sigma_decomposition x` onto `sigma_decomposition (h x h⁻¹)` (via `sigmaPart_conj`),
so the two sets have the same cardinality. -/
theorem sigmaLength_conj [Finite G] (h x : G) :
    sigmaLength (h * x * h⁻¹) = sigmaLength x := by
  have hinj : Function.Injective (fun z => h * z * h⁻¹) := fun a b hab => by simpa using hab
  have hconjset : sigmaDecomposition (h * x * h⁻¹)
      = (fun z => h * z * h⁻¹) '' sigmaDecomposition x := by
    unfold sigmaDecomposition
    rw [Set.image_sdiff hinj]
    congr 1
    · ext y
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨M, hMmax, rfl⟩
        exact ⟨sigmaPart M x, ⟨M, hMmax, rfl⟩, (sigmaPart_conj M h x).symm⟩
      · rintro ⟨z, ⟨M, hMmax, rfl⟩, rfl⟩
        exact ⟨M, hMmax, (sigmaPart_conj M h x).symm⟩
    · rw [Set.image_singleton]; simp
  rw [sigmaLength, sigmaLength, hconjset, Set.ncard_image_of_injective _ hinj]

/-- **Coq `sigma_decomposition_subG`**: if `x ∈ H` then every σ-part of `x` lies in `H` (the σ-parts
are powers of `x`), so `sigma_decomposition x ⊆ H`. -/
theorem sigmaDecomposition_subset [Finite G] {x : G} {H : Subgroup G} (hx : x ∈ H) :
    sigmaDecomposition x ⊆ (H : Set G) := by
  rintro y ⟨⟨M, hM, rfl⟩, -⟩
  exact Subgroup.zpowers_le.mpr hx (piPart_mem_zpowers (OddOrder.BG.Ch3.S10.sigma M) x)

/-- Every element of `M_σ` is a `σ(M)`-element (its order divides `|M_σ|`, a `σ(M)`-number). -/
theorem isPiElement_sigma_of_mem_Msigma [Finite G] {M : Subgroup G} {x : G}
    (hx : x ∈ OddOrder.BG.Ch3.S10.Msigma M) :
    IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
  intro p hp
  have horx : orderOf x = orderOf (⟨x, hx⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    simpa using orderOf_injective (OddOrder.BG.Ch3.S10.Msigma M).subtype
      (OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨x, hx⟩
  have hdvd : orderOf x ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [horx]; exact orderOf_dvd_natCard _
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
    (Nat.primeFactors_mono hdvd (Nat.card_pos).ne' hp)

/-- **`M_σ`-membership is exactly being a `σ(M)`-element** (for `x ∈ M`).  `M_σ` is the *normal*
`σ(M)`-Hall of `M` (`Msigma_isHall`), so it absorbs every `σ(M)`-subgroup; hence `x ∈ M_σ ⟺ ⟨x⟩` is
a `σ(M)`-group `⟺ x` is a `σ(M)`-element.  In particular `M_σ`-membership of an element of `M` is
determined by its order, so it is conjugation-invariant (`isPiElement_conj`) — the BG Theorem E
"distinct orders across pieces" content for the `M_σ` piece. -/
theorem mem_Msigma_iff_isPiElement_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G} (hxM : x ∈ M) :
    x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
  refine ⟨isPiElement_sigma_of_mem_Msigma, fun hpi => ?_⟩
  have hzpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) (Subgroup.zpowers x) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hpi p hp
  exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) (Subgroup.zpowers_le.mpr hxM) hzpi
    (Subgroup.mem_zpowers x)

/-- **An element of `M` whose order is coprime to `[M : N]` lies in the normal `N ≤ M`.**  Pure
group theory: `x^[M:N] ∈ N` (`Subgroup.pow_index_mem`), and `x ∈ ⟨x^[M:N]⟩` because `[M:N]` is
coprime to `orderOf x` (`exists_pow_eq_self_of_coprime`).  The engine for "a normal `π′`-Hall of `M`
absorbs every `π′`-element of `M`" (apply with `[M:N]` a `π`-number and `x` a `π′`-element) — used
for the `A(M)` / `κ(M)′`-Hall piece of BG Theorem E's "distinct orders". -/
theorem mem_of_coprime_index [Finite G] {M N : Subgroup G} (hNM : N ≤ M)
    [(N.subgroupOf M).Normal] {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime ((N.subgroupOf M).index) (orderOf x)) : x ∈ N := by
  have hpow : x ^ (N.subgroupOf M).index ∈ N := by
    have h := Subgroup.pow_index_mem (N.subgroupOf M) ⟨x, hxM⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hpow m

/-- **The index `[M : U ⊔ M_σ]` is a `κ(M)`-number** (`M` maximal, `M_σ` the `σ(M)`-Hall, `U` a
`(κ∪σ)′`-Hall).  Since `M_σ ≤ U ⊔ M_σ` and `U ≤ U ⊔ M_σ`, `[M : U⊔M_σ]` divides both `[M : M_σ]` (a
`σ′`-number, `Msigma_subgroupOf_isHall`) and `[M : U]` (a `κ∪σ`-number, `hU`), so each of its primes
avoids `σ` yet lies in `κ ∪ σ`, i.e. in `κ(M)`.  Combined with `mem_of_coprime_index`, this gives the
`A(M)`-piece absorption "a `κ(M)′`-element of `M` lies in `U ⊔ M_σ`" of BG Theorem E. -/
theorem index_U_sup_Msigma_primeFactors_subset_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p ∈ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index.primeFactors) :
    p ∈ kappa M := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    Nat.dvd_of_mem_primeFactors hp
  have hdvdMσ : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
    Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M le_sup_right)
  have hdvdU : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣ (U.subgroupOf M).index :=
    Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M le_sup_left)
  have hpnσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvdMσ, Subgroup.index_ne_zero_of_finite⟩)
  have hpnκσ : p ∉ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans hdvdU, Subgroup.index_ne_zero_of_finite⟩)
  simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hpnκσ
  exact hpnκσ.resolve_right hpnσ

/-- **`|H ⊔ N|` divides `|H| · |N|`** for `N ◁ G` (Noether's second isomorphism: `[H⊔N : N] =
[H : H⊓N]`, so `|H⊔N| = [H : H⊓N]·|N|` with `[H : H⊓N] ∣ |H|`).  Used to bound `π(U ⊔ M_σ) ⊆ κ′`
from `π(U) ⊆ (κ∪σ)′` and `π(M_σ) ⊆ σ` (the `A(M)`-piece forward, with `M_σ ◁ M`). -/
theorem card_sup_dvd_mul_of_normal {H N : Subgroup G} [N.Normal] :
    Nat.card ↥(H ⊔ N) ∣ Nat.card ↥H * Nat.card ↥N := by
  have e : (N.subgroupOf H).index = (N.subgroupOf (H ⊔ N)).index := by
    have h := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).toEquiv
    simpa [Subgroup.index] using h
  have hN : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h1 : Nat.card ↥(H ⊔ N) = (N.subgroupOf (H ⊔ N)).index * Nat.card ↥N := by
    rw [← Subgroup.card_mul_index (N.subgroupOf (H ⊔ N)), hN, mul_comm]
  rw [h1, ← e]
  exact mul_dvd_mul_right (N.subgroupOf H).index_dvd_card (Nat.card ↥N)

/-- **`U ⊔ M_σ`-membership is exactly being a `κ(M)′`-element** (for `x ∈ M`, given `U⊔M_σ ◁ M` as
`hnorm`).  `U⊔M_σ` is the normal `κ(M)′`-Hall of `M`: forward, `|U⊔M_σ| ∣ |U||M_σ|`
(`card_sup_dvd_mul_of_normal`, `M_σ ◁ M`) and `π(U), π(M_σ) ⊆ κ′`, so any `x ∈ U⊔M_σ` is a
`κ′`-element; backward, `[M:U⊔M_σ]` is a `κ`-number (`index_U_sup_Msigma_primeFactors_subset_kappa`),
coprime to a `κ′`-element's order, so `mem_of_coprime_index` puts it in `U⊔M_σ`.  The `A(M)`-piece of
BG Theorem E's "distinct orders": `U⊔M_σ`-membership of an element of `M` is order-determined. -/
theorem mem_U_sup_Msigma_iff_isPiElement_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal)
    {x : G} (hxM : x ∈ M) :
    x ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ↔ IsPiElement (kappa M)ᶜ x := by
  haveI := hnorm
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  refine ⟨fun hx p hp => ?_, fun hpi => ?_⟩
  · -- forward: `x ∈ U⊔M_σ ⟹` `p ∈ π(orderOf x) ⟹ p ∉ κ`.
    have hpord : p ∣ orderOf x := Nat.dvd_of_mem_primeFactors hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h1 : orderOf x ∣ Nat.card ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M) := by
      have heq : orderOf x = orderOf (⟨x, hx⟩ : ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M)) :=
        orderOf_injective (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subtype
          (U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨x, hx⟩
      rw [heq]; exact orderOf_dvd_natCard _
    have h2 : Nat.card ↥(U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ∣
        Nat.card ↥U * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      haveI : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
        rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
      have hdvd := card_sup_dvd_mul_of_normal (H := U.subgroupOf M)
        (N := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      rw [← Subgroup.subgroupOf_sup hUM hMσM,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hUM hMσM)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv] at hdvd
      exact hdvd
    have hp2 : p ∣ Nat.card ↥U * Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (hpord.trans h1).trans h2
    rcases (hpp.dvd_mul.mp hp2) with hpU | hpMσ
    · have hpfU : p ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv) ▸ hpU, Nat.card_pos.ne'⟩
      have := hU.primeFactors_card_subset p hpfU
      simp only [Set.mem_compl_iff, Set.mem_union, not_or] at this
      exact this.1
    · have hpfMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp,
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv) ▸ hpMσ, Nat.card_pos.ne'⟩
      exact fun hpκ => kappa_subset_sigmaCompl hpκ
        ((OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).primeFactors_card_subset p hpfMσ)
  · -- backward: `κ′`-element of `M` lies in `U⊔M_σ`.
    refine mem_of_coprime_index (sup_le hUM hMσM) hxM ?_
    refine (Nat.disjoint_primeFactors Subgroup.index_ne_zero_of_finite
      (orderOf_pos x).ne').mp ?_
    rw [Finset.disjoint_left]
    intro p hpfκ hpfo
    exact (hpi p hpfo) (index_U_sup_Msigma_primeFactors_subset_kappa hG hM hU hpfκ)

/-- For a `σ(M)`-element `x`, every `σ(L)`-part (`L` maximal) is either `x` or `1`: if `L` is
conjugate to `M` then `σ(L) = σ(M)` contains all primes of `x` (`sigmaPart L x = x`); otherwise
`σ(M) ∩ σ(L) = ∅` (`sigma_disjoint_of_nonconjugate`) so `x` avoids `σ(L)` (`sigmaPart L x = 1`). -/
theorem sigmaPart_eq_self_or_one_of_isPiElement_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) :
    sigmaPart L x = x ∨ sigmaPart L x = 1 := by
  simp only [sigmaPart]
  by_cases hconj : ∃ g : G, MulAut.conj g • M = L
  · obtain ⟨g, rfl⟩ := hconj
    exact Or.inl (piPart_self_of_isPiElement (fun p hp => by
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact OddOrder.BG.Ch3.S10.sigma_conj g (hx p hp)))
  · refine Or.inr (piPart_eq_one_of_isPiElement_compl (fun p hp hpL => ?_))
    exact Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hL hconj) (hx p hp) hpL

/-- **Directed `sigmaPart`, conjugate case**: a `σ(M)`-element is fixed by the `σ(L)`-part when `L`
is `M`-conjugate (`σ(L) = σ(M)`). -/
theorem sigmaPart_eq_self_of_conj [Finite G] {M : Subgroup G} {x : G}
    (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hconj : ∃ g : G, MulAut.conj g • M = L) : sigmaPart L x = x := by
  simp only [sigmaPart]
  obtain ⟨g, rfl⟩ := hconj
  exact piPart_self_of_isPiElement (fun p hp => by
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact OddOrder.BG.Ch3.S10.sigma_conj g (hx p hp))

/-- **Directed `sigmaPart`, non-conjugate case**: a `σ(M)`-element has trivial `σ(L)`-part when `L`
is *not* `M`-conjugate (`σ(M) ∩ σ(L) = ∅`). -/
theorem sigmaPart_eq_one_of_not_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (hnconj : ¬ ∃ g : G, MulAut.conj g • M = L) :
    sigmaPart L x = 1 := by
  simp only [sigmaPart]
  exact piPart_eq_one_of_isPiElement_compl (fun p hp hpL =>
    Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hL hnconj) (hx p hp) hpL)

/-- **σ-decomposition of a `σ`-cover element** (Coq `sigma_cover_decomposition`, BG remark above
Lemma 14.5): for a nonidentity `σ(M)`-element `x`, a `σ(N)`-element `x'` with `M`, `N`
non-conjugate, and `x`, `x'` commuting, `sigma_decomposition (x * x') = {x} ∪ {x'}^#`.  Each `σ(L)`-part
of `x * x'` is `sigmaPart L x · sigmaPart L x'` (`piPart_mul_of_commute`); as `M`, `N` are
non-conjugate, no `L` is conjugate to both, so that part is `x` (`L ∼ M`), `x'` (`L ∼ N`) or `1`. -/
theorem sigma_cover_decomposition [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    (hMN : ¬ ∃ g : G, MulAut.conj g • M = N)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    sigmaDecomposition (x * x') = insert x ({x'} \ {1}) := by
  classical
  have hxσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := isPiElement_sigma_of_mem_Msigma hxM
  have hx'σ : IsPiElement (OddOrder.BG.Ch3.S10.sigma N) x' := isPiElement_sigma_of_mem_Msigma hx'N
  -- conjugacy is symmetric, so `N` is not `M`-conjugate either.
  have hNM : ¬ ∃ g : G, MulAut.conj g • N = M := by
    rintro ⟨g, hg⟩
    exact hMN ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hpart : ∀ L : Subgroup G, sigmaPart L (x * x') = sigmaPart L x * sigmaPart L x' := fun L => by
    simp only [sigmaPart]; exact piPart_mul_of_commute hcomm
  ext y
  simp only [sigmaDecomposition, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨⟨L, hL, rfl⟩, hne⟩
    rw [hpart L] at hne ⊢
    by_cases hLM : ∃ g : G, MulAut.conj g • M = L
    · by_cases hLN : ∃ g : G, MulAut.conj g • N = L
      · exfalso
        obtain ⟨g, hg⟩ := hLM; obtain ⟨h, hh⟩ := hLN
        refine hMN ⟨h⁻¹ * g, ?_⟩
        have hgh : MulAut.conj g • M = MulAut.conj h • N := hg.trans hh.symm
        rw [map_mul, mul_smul, hgh, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      · left
        rw [sigmaPart_eq_self_of_conj hxσ hLM,
          sigmaPart_eq_one_of_not_conj hG hN hx'σ hL hLN, mul_one]
    · by_cases hLN : ∃ g : G, MulAut.conj g • N = L
      · right
        have hval : sigmaPart L x * sigmaPart L x' = x' := by
          rw [sigmaPart_eq_one_of_not_conj hG hM hxσ hL hLM,
            sigmaPart_eq_self_of_conj hx'σ hLN, one_mul]
        exact ⟨hval, hval ▸ hne⟩
      · exact absurd (by rw [sigmaPart_eq_one_of_not_conj hG hM hxσ hL hLM,
          sigmaPart_eq_one_of_not_conj hG hN hx'σ hL hLN, mul_one]) hne
  · rintro (rfl | ⟨rfl, hne⟩)
    · refine ⟨⟨M, hM, ?_⟩, hx1⟩
      rw [hpart M, sigmaPart_eq_self_of_conj hxσ ⟨1, by rw [map_one, one_smul]⟩,
        sigmaPart_eq_one_of_not_conj hG hN hx'σ hM hNM, mul_one]
    · refine ⟨⟨N, hN, ?_⟩, hne⟩
      rw [hpart N, sigmaPart_eq_one_of_not_conj hG hM hxσ hN hMN,
        sigmaPart_eq_self_of_conj hx'σ ⟨1, by rw [map_one, one_smul]⟩, one_mul]

/-- **The signalizer maximal is not `M`-conjugate** (the `M, N` non-conjugacy behind the cover
decomposition): a nonidentity `σ(M)`-element `x` that is also a `τ₂(N)`-element forces `M`, `N`
non-conjugate.  If `M ∼ N` then `σ(M) = σ(N)`, so a prime `q ∣ |x|` lies in `σ(N)`; but `q ∈ τ₂(N) ⊆
σ(N)ᶜ` (`tau2_subset_sigma_compl`) — contradiction.  In the FT signalizer context `x ∈ M_σ^#` is a
`τ₂(N)`-element for the signalizer maximal `N` (`signalizer_structure_of_mem_sigmaSharp`). -/
theorem not_conj_of_mem_Msigma_of_tau2 [Finite G] {M N : Subgroup G}
    {x : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N) :
    ¬ ∃ g : G, MulAut.conj g • M = N := by
  rintro ⟨g, hg⟩
  obtain ⟨q, hqp, hqdvd⟩ :=
    (orderOf x).exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
  haveI : Fact q.Prime := ⟨hqp⟩
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    isPiElement_sigma_of_mem_Msigma hxM q (Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩)
  have hqσN : q ∈ OddOrder.BG.Ch3.S10.sigma N := hg ▸ OddOrder.BG.Ch3.S10.sigma_conj g hqσM
  have hcardx : Nat.card ↥(Subgroup.closure ({x} : Set G)) = orderOf x := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hqπ : q ∈ piSet (Subgroup.closure ({x} : Set G)) := by
    rw [piSet, Set.mem_setOf_eq, hcardx]
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩
  exact tau2_subset_sigma_compl N (hxτ2 q hqπ) hqσN

/-- **σ-decomposition of a cover element in the signalizer context** (`sigma_cover_decomposition`
specialized to `N` = the signalizer maximal): for `x ∈ M_σ^#` a `τ₂(N)`-element and `x' ∈ N_σ`
commuting with `x`, `sigma_decomposition (x * x') = {x} ∪ {x'}^#`.  The `M, N` non-conjugacy needed by
`sigma_cover_decomposition` is supplied by `not_conj_of_mem_Msigma_of_tau2`.  Discharges the cover
decomposition that BG Lemma 14.5(a) (`sigma_cover_disjoint`) reads off. -/
theorem sigma_cover_decomposition_signalizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    sigmaDecomposition (x * x') = insert x ({x'} \ {1}) :=
  sigma_cover_decomposition hG hM hN (not_conj_of_mem_Msigma_of_tau2 hxM hx1 hxτ2) hxM hx1 hx'N hcomm

/-- **`x` is a `σ`-part of the cover element `x · x'`** (Coq `mem_sigma_cover_decomposition`): immediate
from `sigma_cover_decomposition_signalizer`, `x ∈ {x} ∪ {x'}^#`.  Used in BG Lemma 14.5(a). -/
theorem mem_sigma_cover_decomposition_signalizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    x ∈ sigmaDecomposition (x * x') := by
  rw [sigma_cover_decomposition_signalizer hG hM hN hxM hx1 hxτ2 hx'N hcomm]
  exact Set.mem_insert x _

/-- **BG Corollary 14.10 (cover form): `ℓ_σ(x · x') ≤ 2`** (Coq `ell_sigma_cover`): a `σ`-cover
element has `σ`-length at most two, since its `σ`-decomposition `{x} ∪ {x'}^#` has at most two
elements (`sigma_cover_decomposition_signalizer`). -/
theorem sigmaLength_cover_le_two_signalizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    {x x' : G} (hxM : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hxτ2 : ∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N)
    (hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N) (hcomm : Commute x x') :
    sigmaLength (x * x') ≤ 2 := by
  rw [sigmaLength, sigma_cover_decomposition_signalizer hG hM hN hxM hx1 hxτ2 hx'N hcomm]
  have h1 : ({x'} \ {1} : Set G).ncard ≤ 1 :=
    (Set.ncard_le_ncard Set.sdiff_subset (Set.finite_singleton x')).trans
      (le_of_eq (Set.ncard_singleton x'))
  calc (insert x ({x'} \ {1} : Set G)).ncard
      ≤ ({x'} \ {1} : Set G).ncard + 1 := Set.ncard_insert_le x _
    _ ≤ 2 := by omega

/-- **BG `Msigma_ell1`** (Coq BGsection14): a nonidentity element of `M_σ` has σ-length `1`.  As a
`σ(M)`-element, its σ-decomposition collapses to the single block `{x}`: every `σ(L)`-part is `x`
or `1` (`sigmaPart_eq_self_or_one_of_isPiElement_sigma`), and `sigmaPart M x = x ≠ 1`.  This is the
genuine form of the `ℓ_σ(x) = 1` property that the `SigmaDecompositionData` scaffold posits for
`x ∈ M_σ^#` (`length_one_of_isPiElement_sigma`). -/
theorem Msigma_ell1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hx : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) :
    sigmaLength x = 1 := by
  have hxσ : IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := isPiElement_sigma_of_mem_Msigma hx
  have hself : sigmaPart M x = x := piPart_self_of_isPiElement hxσ
  have hset : sigmaDecomposition x = {x} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨M, hM, hself.symm⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_singleton_iff]; exact hx1
    · rintro y ⟨⟨L, hL, rfl⟩, hy⟩
      rcases sigmaPart_eq_self_or_one_of_isPiElement_sigma hG hM hxσ hL with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mpr h) hy
  rw [sigmaLength, hset, Set.ncard_singleton]

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
      exact hpκ ⟨hp, hpτ13, A, hAr1, hAM, hne⟩
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

/-- Helper for `Msigma_centralizer_E23_eq_bot_of_caseTau1`: a maximal-rank elementary abelian
`p`-subgroup `A ≤ M` satisfying Lemma 14.1's hypotheses (`p ∈ π(M) ∖ (σ(M) ∪ κ(M))`) gives
`C_{M_σ}(A) = 1` (Lemma 14.1); since `A ≤ U`, centralizer antitonicity lifts this to
`C_{M_σ}(U) ≤ C_{M_σ}(A) = 1`. -/
private theorem msigma_centralizer_eq_bot_of_elemAb_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {U A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ piSet M) (hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M) (hpκ : p ∉ kappa M)
    (hA : A ∈ elemAbelianOfRank G p (pRank ↥M p)) (hAM : A ≤ M) (hAU : A ≤ U) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  obtain ⟨_, hCA, hnilp⟩ := msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hA hAM
  refine ⟨?_, hnilp⟩
  rw [eq_bot_iff, ← hCA]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAU))

/-- Helper for `Msigma_centralizer_E23_eq_bot_of_caseTau1`, case `E₃ = ⊥`: for `q ∈ τ₂(M)` and a
`q`-element `y' ∈ E₂#`, `Ω₁(E₂)` is a rank-two elementary abelian `q`-subgroup *of `E₂`* (not just
`E`) containing `y'`.  Same as `exists_elemAb_rank_two_le_E_mem_of_tau2` but exposes the stronger
containment `A ≤ E₂`, which the `U = E₂E₃ = E₂` reduction needs. -/
private theorem exists_elemAb_rank_two_le_E2_mem_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {q : ℕ} [Fact q.Prime] (hq : q ∈ tau2 M)
    {y' : G} (hy'E2 : y' ∈ E₂) (hy'q : y' ^ q = 1) (hy'1 : y' ≠ 1) :
    ∃ A ∈ elemAbelianOfRank G q 2, A ≤ E₂ ∧ y' ∈ A := by
  classical
  have hE2comm : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG h).2.1.1
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE2comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set A : Subgroup G := omega1OfAbelian G E₂ q hcomm with hAdef
  have hAelem : A.IsElementaryAbelian q := omega1OfAbelian_isElementaryAbelian
  have hAE2 : A ≤ E₂ := omega1OfAbelian_le
  have hy'A : y' ∈ A := (mem_omega1OfAbelian).mpr ⟨hy'E2, hy'q⟩
  -- `r_q(E₂) = 2`: two `q`-coprime index steps `E₂ ≤ E ≤ M`, then `r_q(M) = 2`.
  have hpRankE2 : pRank ↥E₂ q = 2 := by
    have hr1 : pRank ↥E₂ q = pRank ↥E q :=
      pRank_eq_of_le_of_not_dvd_index h.E₂_le (fun hdvd =>
        h.E₂_hall.index_no_pi q (Nat.mem_primeFactors.mpr
          ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hq)
    have hr2 : pRank ↥E q = pRank ↥M q := by
      refine pRank_eq_of_le_of_not_dvd_index h.E_le (fun hdvd => ?_)
      have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hq
      have hidxeq : (E.subgroupOf M).index = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [h.isComplement'_subgroupOf.index_eq_card,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      rw [hidxeq] at hdvd
      exact hqσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    rw [hr1, hr2, tau2_pRank_eq_two hq]
  -- `|A| = q²` from `q² ∣ |A|` (rank ≥ 2) and `log_q |A| ≤ r_q(E₂) = 2`.
  have hAcard : Nat.card ↥A = q ^ 2 := by
    have hdvd : q ^ 2 ∣ Nat.card ↥A :=
      hAdef ▸ pow_dvd_card_omega1OfAbelian_of_pos_le_pRank (by norm_num) hpRankE2.ge
    have hlog_le : Nat.log q (Nat.card ↥A) ≤ 2 := by
      have hAsub : (A.subgroupOf E₂).IsElementaryAbelian q :=
        IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAE2).symm hAelem
      have hcardeq : Nat.card ↥(A.subgroupOf E₂) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE2).toEquiv
      have hle := le_pRank (A.subgroupOf E₂) hAsub
      rwa [hcardeq, hpRankE2] at hle
    have hcardpow : Nat.card ↥A = q ^ Nat.log q (Nat.card ↥A) := by
      rw [hAelem.log_card_eq_finrank, hAelem.card_eq_pow_finrank]
    have h2le : 2 ≤ Nat.log q (Nat.card ↥A) := by
      rw [hcardpow] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : q.Prime).one_lt).mp hdvd
    rw [hcardpow]; congr 1; omega
  exact ⟨A, ⟨hAelem, hAcard⟩, hAE2, hy'A⟩

/-- **`C_{M_σ}(U) = 1`** for `U = E₂E₃` in case `τ₁` (BG Lemma 14.1 bridge).  `U` is a Hall
`(κ(M) ∪ σ(M))'`-subgroup; picking any prime `p ∈ π(U)` and a maximal-rank elementary abelian
`p`-subgroup `A ≤ U`, Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`) gives `C_{M_σ}(A) = 1`,
and `C_{M_σ}(U) ≤ C_{M_σ}(A)`.  (In case `τ₁`, `κ(M) ∩ τ₃(M) = ∅` ensures `π(U) ∩ κ(M) = ∅`.)
This is the `C_{M_σ}(U) = 1` hypothesis Proposition 14.2(g) feeds to Theorem 3.10(a).

Proof: since `U = E₂E₃ ≠ 1`, either `E₃ ≠ 1` or `E₂ ≠ 1`.  If `E₃ ≠ 1`, a prime `p ∣ |E₃|`
lies in `τ₃(M)` (as `E₃` is Hall `τ₃(M)` of `E`) with `r_p(M) = 1`, and a cyclic `A = ⟨g⟩ ≤ E₃`
of order `p` is rank-one elementary abelian; `p ∉ κ(M)` because `κ(M) ∩ τ₃(M) = ∅`.  If `E₃ = 1`
then `U = E₂ ≠ 1`; a prime `q ∣ |E₂|` lies in `τ₂(M)` with `r_q(M) = 2`, and `A = Ω₁(E₂) ≤ E₂`
is rank-two elementary abelian; `q ∉ κ(M) ⊆ τ₁(M) ∪ τ₃(M)` since `r_q(M) = 2 ≠ 1`.  Either way
Lemma 14.1 (via `msigma_centralizer_eq_bot_of_elemAb_le`) closes the goal. -/
theorem Msigma_centralizer_E23_eq_bot_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty)
    (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) = ⊥ ∧
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  by_cases hE3 : E₃ = ⊥
  · -- Case `E₃ = ⊥`: `U = E₂E₃ = E₂ ≠ ⊥`; pick `q ∈ τ₂(M)` and `A = Ω₁(E₂)` of rank two.
    have hE2 : E₂ ≠ ⊥ := by
      intro hb; exact hUne (by rw [hb, hE3, bot_sup_eq])
    have hcard2 : Nat.card ↥E₂ ≠ 1 := fun hc => hE2 (Subgroup.card_eq_one.mp hc)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard2
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₂) q hqdvd
    have hy'E2 : (y' : G) ∈ E₂ := y'.2
    have hy'ord : orderOf (y' : G) = q :=
      (orderOf_injective E₂.subtype E₂.subtype_injective y').trans hy'
    have hy'q : (y' : G) ^ q = 1 := by rw [← hy'ord]; exact pow_orderOf_eq_one _
    have hy'1 : (y' : G) ≠ 1 := by
      intro hc; rw [hc, orderOf_one] at hy'ord; exact hq.ne_one hy'ord.symm
    -- `q ∈ τ₂(M)`: `q ∣ |E₂|`, and `E₂` is Hall `τ₂(M)` of `E`.
    have hqE2 : q ∈ (Nat.card ↥E₂).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
    have hqτ2 : q ∈ tau2 M := by
      have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
      exact h.E₂_hall.1 q (hc2 ▸ hqE2)
    -- rank-two `A = Ω₁(E₂) ≤ E₂`.
    obtain ⟨A, hAmem, hAE2, _⟩ :=
      exists_elemAb_rank_two_le_E2_mem_of_tau2 hG h hqτ2 hy'E2 hy'q hy'1
    have hAM : A ≤ M := hAE2.trans (h.E₂_le.trans h.E_le)
    have hArank : A ∈ elemAbelianOfRank G q (pRank ↥M q) := by
      rw [tau2_pRank_eq_two hqτ2]; exact hAmem
    have hpπ : q ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hq,
        hqdvd.trans (Subgroup.card_dvd_of_le (h.E₂_le.trans h.E_le)), Nat.card_pos.ne'⟩
    have hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hqτ2
    -- `q ∉ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`: `r_q(M) = 2`, but `τ₁, τ₃` have `r = 1`.
    have hqκ : q ∉ kappa M := by
      intro hqκ
      have hr2 := tau2_pRank_eq_two hqτ2
      rcases kappa_subset_tau1_union_tau3 hqκ with hτ1 | hτ3'
      · have := tau1_pRank_eq_one hτ1; omega
      · have := tau3_pRank_eq_one hτ3'; omega
    have hAU : A ≤ (E₂ ⊔ E₃ : Subgroup G) := hAE2.trans le_sup_left
    exact msigma_centralizer_eq_bot_of_elemAb_le hG h.mem_maximal hpπ hqσ hqκ hArank hAM hAU
  · -- Case `E₃ ≠ ⊥`: pick `p ∈ τ₃(M)` and a cyclic rank-one `A = ⟨g⟩ ≤ E₃`.
    have hcard3 : Nat.card ↥E₃ ≠ 1 := fun hc => hE3 (Subgroup.card_eq_one.mp hc)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard3
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥E₃) p hpdvd
    have hgE3 : (g : G) ∈ E₃ := g.2
    have hgord : orderOf (g : G) = p :=
      (orderOf_injective E₃.subtype E₃.subtype_injective g).trans hg
    have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by rw [Nat.card_zpowers]; exact hgord
    have hAE3 : Subgroup.zpowers (g : G) ≤ E₃ := Subgroup.zpowers_le.mpr hgE3
    have hAr1 : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
    -- `p ∈ τ₃(M)`: `p ∣ |E₃|`, and `E₃` is Hall `τ₃(M)` of `E`.
    have hpE3 : p ∈ (Nat.card ↥E₃).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
    have hpτ3 : p ∈ tau3 M := by
      have hc3 : Nat.card ↥(E₃.subgroupOf E) = Nat.card ↥E₃ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
      exact h.E₃_hall.1 p (hc3 ▸ hpE3)
    have hAM : Subgroup.zpowers (g : G) ≤ M := hAE3.trans (h.E₃_le.trans h.E_le)
    have hArank : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [tau3_pRank_eq_one hpτ3]; exact hAr1
    have hpπ : p ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le
        (h.E₃_le.trans h.E_le)), Nat.card_pos.ne'⟩
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := tau3_subset_sigma_compl M hpτ3
    -- `p ∉ κ(M)`: `κ(M) ∩ τ₃(M) = ∅` and `p ∈ τ₃(M)`.
    have hpκ : p ∉ kappa M := fun hpκ => hτ3 ⟨p, hpκ, hpτ3⟩
    have hAU : Subgroup.zpowers (g : G) ≤ (E₂ ⊔ E₃ : Subgroup G) := hAE3.trans le_sup_right
    exact msigma_centralizer_eq_bot_of_elemAb_le hG h.mem_maximal hpπ hpσ hpκ hArank hAM hAU

/-- **BG Proposition 14.2(g), TI conjunct** (mmd L3850): if `σ(M) = β(M)` then `M_σ^#` is a
TI-subset of `G` with normalizer-bound `N_G(M_σ)`.  For `g` producing an overlap of `M_σ^#`
with its `g`-conjugate, either `g ∈ M ≤ N_G(M_σ)`, or `g ∉ M` and Lemma 12.17
(`Msigma_inf_conj_isBetaCompl`) makes `M_σ ∩ M_σ^g` a `β(M)′ = σ(M)′`-group; being also a
`σ(M)`-group (`≤ M_σ`) it is trivial, contradicting the nontrivial overlap.  This is the
TI clause Proposition 14.2(g) concludes from `β(M) = σ(M)`. -/
theorem isTISubset_sigmaSharp_of_sigma_eq_beta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M) :
    IsTISubset (sigmaSharp M)
      (Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)) := by
  intro g hov
  obtain ⟨a, haS, hgaS⟩ := hov
  simp only [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff,
    SetLike.mem_coe] at haS hgaS
  obtain ⟨haMσ, _ha1⟩ := haS
  obtain ⟨hgaMσ, hga1⟩ := hgaS
  by_cases hgM : g ∈ M
  · exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hgM
  · exfalso
    -- `g a g⁻¹ ∈ M_σ ∩ (conj g • M_σ)`, nontrivial.
    have hgaConj : g * a * g⁻¹ ∈ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using haMσ
    have hmemInf : g * a * g⁻¹ ∈
        OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M :=
      Subgroup.mem_inf.mpr ⟨hgaMσ, hgaConj⟩
    have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓
        MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M) ≠ 1 := fun h =>
      hga1 (Subgroup.mem_bot.mp ((Subgroup.card_eq_one.mp h) ▸ hmemInf))
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
    haveI : Fact p.Prime := ⟨hp⟩
    -- `p ∈ σ(M)` since the intersection is `≤ M_σ`.
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
        ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    -- `p ∉ β(M)` by Lemma 12.17, since the intersection is `≤ M_σ ⊓ M^g`.
    have hle : OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M ≤
        OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • M :=
      inf_le_inf_left _ (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
        (OddOrder.BG.Ch3.S10.Msigma_le M))
    have hpβ := OddOrder.BG.Ch3.S12.Msigma_inf_conj_isBetaCompl hG hM hgM p
      (Nat.mem_primeFactors.mpr ⟨hp, hpdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)
    exact hpβ (hσβ ▸ hpσ)

/-- **BG Proposition 14.2(g), Frobenius core** (mmd L3850): in case `κ ⊆ τ₁` with `E₁ = K`
non-regular prime on `M_σ` and `U = E₂E₃ ≠ 1`, the type-`P₂` conclusions `σ(M) = β(M)` and
`|K|` prime hold.  `E = E₁ ⋉ U` is a Frobenius group (`isFrobeniusGroup_E_of_caseTau1`) with
`C_{M_σ}(U) = 1` and `M_σ` nilpotent (`Msigma_centralizer_E23_eq_bot_of_caseTau1`); since `E₁`
is prime on the nilpotent `M_σ`, Theorem 3.10(a) gives `|E₁|` prime.  Coprime fixed-point-free
action gives `U = [U, E₁] ≤ E'` (`le_commutator_of_coprime_inf_centralizer_eq_bot`), so `U`
is abelian (Corollary 12.10(b): `E'` abelian) and, by Lemma 12.19, `U` centralizes a Hall
`β(M)'`-subgroup `W` of `M_σ`; `W ≤ C_{M_σ}(U) = 1`, so `M_σ` is a `β(M)`-group, forcing
`σ(M) = β(M)`. -/
theorem sigma_eq_beta_and_prime_card_E1_of_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    (hKstar : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) (hUne : (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
      ∃ q : ℕ, q.Prime ∧ Nat.card ↥E₁ = q := by
  classical
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hUleE_sup : (E₂ ⊔ E₃ : Subgroup G) ≤ E := sup_le h.E₂_le h.E₃_le
  -- `E = E₁ ⋉ U` is Frobenius; `C_{M_σ}(U) = 1` and `M_σ` is nilpotent.
  have hfrob := isFrobeniusGroup_E_of_caseTau1 hG h hE1ne hKstar hτ3 hUne
  obtain ⟨hCU, hMnilp⟩ := Msigma_centralizer_E23_eq_bot_of_caseTau1 hG h hτ3 hUne
  -- `M_σ ≠ ⊥`.
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := fun hb => hKstar (by rw [hb, bot_inf_eq])
  -- Coprime `|E₁|` and `|U|` (Frobenius kernel/complement).
  have hcopKU : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥(E₂ ⊔ E₃)) := by
    have hc := (hfrob.coprime_card_kernel_complement).symm
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE_sup).toEquiv] at hc
  -- `C_U(E₁) = ⊥` (regular action of `E₁` on `U`).
  have hCUK : (E₂ ⊔ E₃ : Subgroup G) ⊓ Subgroup.centralizer (E₁ : Set G) = ⊥ := by
    obtain ⟨⟨g₀, hg₀E1⟩, hg₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1ne
    have hg₀1 : g₀ ≠ 1 := fun hc => hg₀ne (Subtype.ext hc)
    have hr := actsRegularlyOn_E23_E1_of_caseTau1 hG h hE1ne hKstar hτ3 g₀ hg₀E1 hg₀1
    rw [fixedByElement_def] at hr
    rw [eq_bot_iff, ← hr]
    exact inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg₀E1))
  -- **Task B**: `U = [U, E₁] ≤ E'`.
  haveI hE1solv : IsSolvable ↥E₁ :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (h.E₁_le.trans h.E_le))
  have hUleE' : (E₂ ⊔ E₃ : Subgroup G) ≤ derivedInG E := by
    have hUcomm : (E₂ ⊔ E₃ : Subgroup G) ≤ ⁅E₁, E₂ ⊔ E₃⁆ :=
      OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot
        (h.E₁_le.trans (h.E23_normal hG)) hcopKU hCUK
    have hcomm_le : (⁅E₁, E₂ ⊔ E₃⁆ : Subgroup G) ≤ ⁅E, E⁆ :=
      Subgroup.commutator_mono h.E₁_le hUleE_sup
    exact hUcomm.trans (le_of_le_of_eq hcomm_le (Subgroup.map_subtype_commutator E).symm)
  -- `U` is abelian (`U ≤ E'` and `E'` is abelian by Corollary 12.10(b)).
  have hE'ab : IsMulCommutative ↥(derivedInG E) := (nilpotent_sigmaComplement_abelian hG h).2.1.2
  have hUab : ∀ a b : ↥(E₂ ⊔ E₃), (a : G) * (b : G) = (b : G) * (a : G) := fun a b =>
    congrArg Subtype.val (hE'ab.is_comm.comm ⟨a, hUleE' a.2⟩ ⟨b, hUleE' b.2⟩)
  -- `E₁` is prime on `M_σ` ⟹ the `hcond3` hypothesis of Theorem 3.10(a).
  have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  have hcond3 : ∀ x ∈ E₁, x ≠ 1 →
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) =
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) := by
    intro x hx hx1
    have := hE1prime x hx hx1
    rwa [fixedByElement_def, fixedBy_def] at this
  -- `E ≤ N_G(M_σ)`, coprime `|E|` `|M_σ|`, and `M_σ ⊔ E` solvable.
  have hEMσ : E ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    h.E_le.trans (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
  have hcopEMσ : Nat.Coprime (Nat.card ↥E) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have h1 := (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG h.mem_maximal).coprime_index
    rw [h.isComplement'_subgroupOf.symm.index_eq_card] at h1
    rw [Nat.coprime_comm] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv] at h1
  haveI hsolvME : IsSolvable ↥(OddOrder.BG.Ch3.S10.Msigma M ⊔ E) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective (sup_le hMσM h.E_le))
  -- **Theorem 3.10(a)**: `|E₁|` has prime order.
  have hKprime : ∃ q : ℕ, q.Prime ∧ Nat.card ↥E₁ = q :=
    OddOrder.BG.Ch1.S03.prime_card_complement_of_frobenius_conj hsolvME hUleE_sup h.E₁_le hfrob
      hUab hEMσ hMnilp hMσne hcopEMσ hCU hcond3
  -- **σ = β**: Lemma 12.19 gives `W` a Hall `β'`-subgroup of `M_σ` with `E' ≤ C_G(W)`; since
  -- `U ≤ E'` we get `W ≤ C_{M_σ}(U) = 1`, so `M_σ` is a `β(M)`-group, forcing `σ(M) = β(M)`.
  obtain ⟨W, hWMσ, hWHall, hE'centW⟩ :=
    OddOrder.BG.Ch3.S12.derivedE_centralizes_betaComplement hG h
  have hWcentU : W ≤ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (hE'centW (hUleE' hu))) w hw).symm
  have hWbot : W = ⊥ := by
    have hWle : W ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := le_inf hWMσ hWcentU
    rw [hCU] at hWle; exact le_bot_iff.mp hWle
  have hπMσβ : ∀ p ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).primeFactors,
      p ∈ OddOrder.BG.Ch3.S10.beta M := by
    intro p hp
    have hidx : (W.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
      rw [hWbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    have hmem := hWHall.2 p (hidx ▸ hp)
    simp only [Set.mem_compl_iff, not_not] at hmem
    exact hmem
  have hσβ : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M := by
    refine Set.eq_of_subset_of_subset (fun p hp => ?_) (fun p hp =>
      OddOrder.BG.Ch3.S10.alpha_subset_sigma hG h.mem_maximal
        (OddOrder.BG.Ch3.S10.beta_subset_alpha M hp))
    -- `σ ⊆ β`: `p ∈ σ ⟹ p ∣ |M_σ|` (Hall) `⟹ p ∈ β`.
    refine hπMσβ p ?_
    obtain ⟨hpπM, _⟩ := (OddOrder.BG.Ch3.S10.mem_sigma_iff M p).mp hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpπM
    refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
    by_contra hndvd
    have hHall := OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG h.mem_maximal
    have hcardM := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    have hcardeq : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
        Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    have hpM : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpπM).2.1
    rw [← hcardM, hcardeq] at hpM
    have hpidx : p ∣ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index :=
      (hpp.dvd_mul.mp hpM).resolve_left hndvd
    exact hHall.2 p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpidx, Subgroup.index_ne_zero_of_finite⟩) hp
  exact ⟨hσβ, hKprime⟩

/-- **BG Proposition 14.2(g), type-`P₂` ⟹ `U ≠ 1`** (mmd L3850, "`M ∈ 𝓜_{𝒫₂}`, i.e. `U ≠ 1`"):
in case `κ ⊆ τ₁` (so `κ(M) = τ₁(M)`), if `E₂E₃ = 1` then `E = E₁ = K`, hence `κ(M)` equals
`π(M) ∖ σ(M)` (every `σ(M)'`-prime of `M` divides `|E| = |E₁|` and lies in `κ` by the prime
action), so `M` is type `P₁`.  The contrapositive: `IsTypeP2 M ⟹ E₂E₃ ≠ 1`. -/
theorem E23_ne_bot_of_isTypeP2_caseTau1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁)
    (hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    (hτ3 : ¬ (kappa M ∩ tau3 M).Nonempty) (hP2 : IsTypeP2 M) :
    (E₂ ⊔ E₃ : Subgroup G) ≠ ⊥ := by
  classical
  intro hUbot
  -- `E = E₁` since `E = E₁E₂E₃` and `E₂ = E₃ = ⊥`.
  have hE2bot : E₂ = ⊥ := le_bot_iff.mp (le_sup_left.trans hUbot.le)
  have hE3bot : E₃ = ⊥ := le_bot_iff.mp (le_sup_right.trans hUbot.le)
  have hEeq : E = E₁ := by
    rw [h.eq_sup hG, hE2bot, hE3bot, sup_bot_eq, sup_bot_eq]
  -- `κ(M) = π(M) ∖ σ(M)`, contradicting `IsTypeP2 M`.
  refine absurd ?_ hP2.2
  apply Set.eq_of_subset_of_subset
  · -- `κ(M) ⊆ π(M) ∖ σ(M)`.
    intro p hpκ
    obtain ⟨hpp, hpτ, P, hPelem, hPM, _⟩ := hpκ
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      rcases hpτ with hp | hp
      · exact tau1_subset_sigma_compl M hp
      · exact tau3_subset_sigma_compl M hp
    exact ⟨Nat.mem_primeFactors.mpr
      ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩, hpσ⟩
  · -- `π(M) ∖ σ(M) ⊆ κ(M)`: `p ∣ |M|`, `p ∉ σ` ⟹ `p ∣ |E| = |E₁|` ⟹ `p ∈ κ`.
    intro p hp
    obtain ⟨hpπ, hpσ⟩ := hp
    obtain ⟨hpp, hpdvdM, _⟩ := Nat.mem_primeFactors.mp hpπ
    haveI : Fact p.Prime := ⟨hpp⟩
    have hpnMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
      hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
        (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
    have hdvdME : p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
      rw [h.card_Msigma_mul_card_E]; exact hpdvdM
    have hpE1 : p ∈ (Nat.card ↥E₁).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpp, hEeq ▸ (hpp.dvd_mul.mp hdvdME).resolve_left hpnMσ, Nat.card_pos.ne'⟩
    exact mem_kappa_of_mem_primeFactors_card_E1 hG h hE1prime hCE1 hpE1

/-- **BG Proposition 14.2(e), second clause `S ⊄ K*`** (mmd L3828, proof L3846).  In a type-`P`
`E`-setup whose `τ₁`-Hall `E₁` lies in the `κ(M)`-subgroup `K` (so `K` is a `τ₁∪τ₃`-group and
`K* = C_{M_σ}(K)`), no Sylow `q`-subgroup `S` of `M_σ` is contained in `K*`.

This is the linchpin of Corollary 15.3(a): with it one shows `C_M(H)` is a `κ(M)'`-group for every
nontrivial Hall subgroup `H` of `M_σ` (if `H ≤ K*`, a Sylow `S ≤ H ≤ K*` of `M_σ` violates this).
It strengthens — and now subsumes — `kstar_ne_msigma_aux` (`K* ≠ M_σ`).

Proof (BG L3846).  **Part A** (`ℳ(K*) ≠ {M}`): pick `p₀ ∈ π(K)` and `X ∈ ℰ_{p₀}¹(K)`; then
`C_{M_σ}(X) ⊇ K* ≠ 1`, so Lemma 13.13 (`mem_sigma_of_tau1_tau3_centralize`), applied to a maximal
`Mi ⊇ N_G(X)`, gives `p₀ ∈ σ(Mi)`; as `p₀ ∈ τ₁∪τ₃ ⊆ σ(M)'` we get `Mi ≠ M`, and
`K* ≤ C_G(X) ≤ N_G(X) ≤ Mi`.  **Part B**: if `S ≤ K*`, take `X_S ∈ ℰ_q¹(S) ⊆ ℰ_q¹(K*)`; since
`E₁ ≤ K`, `X_S ≤ M_σ ⊓ C(E₁)`, so Lemma 13.6 (`maximalContaining_eq_singleton_of_E1`, `P = E₁`)
gives `ℳ(S) = {M}`; but `S ≤ K* ≤ Mi` forces `Mi ∈ ℳ(S) = {M}`, i.e. `Mi = M`, a contradiction. -/
theorem typeP_sylow_not_le_kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ K Kstar : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1K : E₁ ≤ K) (hKE : K ≤ E) (hE1ne : E₁ ≠ ⊥) (hKne : K ≠ ⊥)
    (hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥)
    {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hSne : S ≠ ⊥)
    (hSle : S ≤ OddOrder.BG.Ch3.S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    ¬ S ≤ Kstar := by
  classical
  intro hSK
  -- ## Part A: `ℳ(K*) ≠ {M}` — some maximal `Mi ≠ M` contains `K*`.
  obtain ⟨p₀, hp₀, hp₀dvd⟩ :=
    (Nat.card ↥K).exists_prime_and_dvd (fun hc => hKne (Subgroup.card_eq_one.mp hc))
  haveI : Fact p₀.Prime := ⟨hp₀⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p₀ hp₀dvd
  have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = p₀ := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ K.subtype_injective w).trans hw
  have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G p₀ 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (w : G) ≤ K := Subgroup.zpowers_le.mpr w.2
  have hXne : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXM : Subgroup.zpowers (w : G) ≤ M := (hXK.trans hKE).trans h.E_le
  have hp₀τ13 : p₀ ∈ tau1 M ∪ tau3 M :=
    hKpi13 p₀ (Nat.mem_primeFactors.mpr ⟨hp₀, hp₀dvd, Nat.card_pos.ne'⟩)
  have hKstar_le_inf : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) := by
    rw [hKstar]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
  have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) ≠ ⊥ :=
    fun hbot => hKstar_ne (le_bot_iff.mp (hKstar_le_inf.trans hbot.le))
  have hNlt : Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hXM hXne
  obtain ⟨Mi, hMico, hNMi⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G))).resolve_left
      hNlt.ne
  have hMimem : Mi ∈ maximalSubgroupsContaining
      (Subgroup.normalizer ((Subgroup.zpowers (w : G)) : Set G)) := ⟨hMico, hNMi⟩
  have hp₀σMi : p₀ ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    mem_sigma_of_tau1_tau3_centralize hG h hp₀τ13 hXelem ((hXK.trans hKE)) hCX hMimem
  have hMineM : Mi ≠ M := by
    intro hMieq
    have hp₀σM : p₀ ∈ OddOrder.BG.Ch3.S10.sigma M := hMieq ▸ hp₀σMi
    have hp₀nσM : p₀ ∉ OddOrder.BG.Ch3.S10.sigma M :=
      hp₀τ13.elim (fun hh => tau1_subset_sigma_compl M hh) (fun hh => tau3_subset_sigma_compl M hh)
    exact hp₀nσM hp₀σM
  have hKstar_le_Mi : Kstar ≤ Mi :=
    ((hKstar_le_inf.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)).trans hNMi
  -- ## Part B: `S ≤ K*` contradicts `ℳ(S) = {M}` (Lemma 13.6).
  -- `q ∣ |S|` (nontrivial `q`-group), so pick `X_S ∈ ℰ_q¹(S)`.
  have hqdvdS : q ∣ Nat.card ↥S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSq
    rw [hk]
    refine dvd_pow_self q ?_
    rintro rfl
    rw [pow_zero] at hk
    exact hSne (Subgroup.card_eq_one.mp hk)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' q hqdvdS
  have hXScard : Nat.card ↥(Subgroup.zpowers (v : G)) = q := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ S.subtype_injective v).trans hv
  have hXSelem : Subgroup.zpowers (v : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXScard, by rw [hXScard, pow_one]⟩
  have hXS_le_S : Subgroup.zpowers (v : G) ≤ S := Subgroup.zpowers_le.mpr v.2
  have hXS_le_Kstar : Subgroup.zpowers (v : G) ≤ Kstar := hXS_le_S.trans hSK
  -- `X_S ≤ M_σ ⊓ C(E₁)` (`X_S ≤ K* = M_σ ⊓ C(K) ≤ M_σ ⊓ C(E₁)`, since `E₁ ≤ K`).
  have hXC : Subgroup.zpowers (v : G) ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (E₁ : Set G) := by
    have h1 : Subgroup.zpowers (v : G) ≤
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := hKstar ▸ hXS_le_Kstar
    exact le_inf (h1.trans inf_le_left)
      ((h1.trans inf_le_right).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hE1K)))
  -- `q ∈ σ(M)` (`X_S ≤ M_σ`).
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hqdvdS.trans (Subgroup.card_dvd_of_le hSle), Nat.card_pos.ne'⟩)
  -- Lemma 13.6: `ℳ(S) = {M}`.
  have hMS : maximalSubgroupsContaining S = {M} :=
    (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hXSelem hXC hSle hSq hSmax).2
  -- `S ≤ K* ≤ Mi`, so `Mi ∈ ℳ(S) = {M}`, i.e. `Mi = M`, contradicting `Mi ≠ M`.
  have hMiS : Mi ∈ maximalSubgroupsContaining S := ⟨hMico, hSK.trans hKstar_le_Mi⟩
  rw [hMS, Set.mem_singleton_iff] at hMiS
  exact hMineM hMiS

/-- **BG Proposition 14.2(e), `K* ⊊ M_σ` form** (mmd L3846).  Immediate corollary of
`typeP_sylow_not_le_kstar`: a Sylow `S` of `M_σ` cannot lie in `K*`, so `K* ≠ M_σ` (else every
`S ≤ M_σ = K*`).  Retained as a named lemma for the `typeP_structure` `(e)` conjunct. -/
theorem kstar_ne_msigma_aux [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ K Kstar : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1K : E₁ ≤ K) (hKE : K ≤ E) (hE1ne : E₁ ≠ ⊥) (hKne : K ≠ ⊥)
    (hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥) :
    Kstar ≠ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  intro hKMσ
  -- Pick `p ∈ π(M_σ)` and a Sylow `S = Syl_p(M_σ)`; then `S ≤ M_σ = K*`, contradicting
  -- `typeP_sylow_not_le_kstar` (`S ⊄ K*`).
  have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ :=
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG h.mem_maximal
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).exists_prime_and_dvd
    (fun hc => hMσne (Subgroup.card_eq_one.mp hc))
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h p
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup p ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hpdvdS : p ∣ Nat.card ↥S := by
      rw [hScard]
      exact dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hpdvd).ne'
    rw [Subgroup.card_eq_one.mpr hSbot] at hpdvdS
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpdvdS)
  exact typeP_sylow_not_le_kstar hG h hE1K hKE hE1ne hKne hKpi13 hKstar hKstar_ne
    hSne hSMσ hSq hSmax (by rw [hKMσ]; exact hSMσ)

/-- **BG Proposition 14.2** (mmd L3778): structure of a type-`P` maximal subgroup
("nearly everything proved in §13" about `M ∈ 𝓜_𝓟`).

`K` = Hall `κ(M)`-subgroup of `M`, `K* = C_{M_σ}(K)`, `U` = Hall `(κ(M) ∪ σ(M))'`-subgroup.
BG states seven parts (a)–(g); this Lean surface is a **faithful partial** capturing the
prime action `(a)`, `K* ≠ 1` `(c)`, the normalizer identity `N_M(X) = K × K*` `(b1)`, the
`(d)` disjointness `K* ∩ M^g = 1` for `g ∉ M`, and the type-`P₂` consequences `(g)`
(`σ = β`, `|K|` prime, `M_σ` a `TI`-subgroup). Deferred to proof time (gated on §13): the
`(a)` regular action on `U` / normal complement `U M_σ`, part `(b2)`, the second half of
`(c)`, the `(d)` clause `K ∩ K^g = 1`, parts `(e)`, `(f)`, and `M_σ` nilpotent in `(g)`.
See `notes/bg/s14_typeP_counting.md` for the full part-map.

**Faithfulness note (2026-06-14):** a spurious `M_σ ≤ N_G(K*)` conjunct was removed — it is
not one of BG's seven parts and is false in general (`K = C_q` acting on a Heisenberg
`M_σ = p^{1+2}` by `a ↦ aʳ, b ↦ b, c ↦ cʳ` gives `K* = ⟨b⟩`, which is **not** normal in
`M_σ` since `a b a⁻¹ = bc ∉ ⟨b⟩`). -/
theorem typeP_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K ∧
      Kstar ≠ ⊥ ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ K →
        Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar) ∧
      (∀ g : G, g ∉ M → Kstar ⊓ (MulAut.conj g • M) = ⊥) ∧
      (IsTypeP2 M → OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.beta M ∧
        ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q ∧
          IsTISubset (sigmaSharp M) (Subgroup.normalizer
            ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G))) ∧
      (∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G p 1 → X ≤ Kstar →
        maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
      Kstar ≠ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  -- `K` is a `σ(M)'`-subgroup (a Hall `κ(M)`-subgroup, and `κ(M) ⊆ σ(M)'`).
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  -- Choose a §12 `E`-setup whose `M_σ`-complement `E` contains `K` (BG: "take `E ⊇ K`").
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  -- BG splits on whether `κ(M) ∩ τ₃(M) = ∅` (i.e. `E₃ ≠ 1` and `E₃` non-regular vs `κ ⊆ τ₁`).
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ(M) ∩ τ₃(M) ≠ ∅`: `E₃` acts non-regularly on `M_σ` (the `κ`-witness conjugates
    -- into `E₃`), so Corollary 13.11 gives `E = E₁ ⊔ E₃`, `E` prime on `M_σ`, and every
    -- `X ∈ ℰ¹(E)` normal in `E`; then `K = E`, and the conjuncts follow.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, hEeq, hEprime, hEnorm⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    -- Extract an `E₃`-witness `x` with `C_{M_σ}(x) ≠ 1` from non-regularity.
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    -- `π(E) ⊆ κ(M)`, so `E` is a `κ(M)`-subgroup; the Hall `κ(M)`-subgroup `K ≤ E` forces `K = E`.
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (a) prime action: immediate from `K = E` and Corollary 13.11.
      rw [hKEeq]; exact hEprime
    · -- `K^* = C_{M_σ}(K) = C_{M_σ}(E) ≠ 1` (prime action + the non-regular witness).
      rw [hKstar, hKEeq]
      exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hEprime hsetup.E₃_le hreg
    · -- (b1) `N_M(X) = K ⊔ K^*` for rank-one `X ≤ K`.  `⊇`: `K = E ≤ N_G(X)` by Corollary 13.11
      -- (`hEnorm`), and `K^* = C_{M_σ}(K) ≤ C_G(X) ≤ N_G(X)`, `K^* ≤ M_σ ≤ M`.  `⊆` (BG "clear",
      -- needs the `M = M_σ ⋊ E` semidirect structure) is deferred.
      intro p hp X hXrank hXK
      haveI : Fact p.Prime := ⟨hp⟩
      refine le_antisymm ?_ ?_
      · -- ⊆: decompose `n = s·e` (`s ∈ M_σ`, `e ∈ E`) in `↥M`; for `g ∈ X#`, `s·(ege⁻¹)·s⁻¹ =
        -- ngn⁻¹ ∈ X ≤ E`, so `[s, ege⁻¹] ∈ M_σ ∩ E = 1`, i.e. `s` centralizes `ege⁻¹ ∈ E#`.
        -- Prime action then gives `s ∈ C_{M_σ}(E) = K*`, and `e ∈ E = K`.
        intro n hn
        rw [Subgroup.mem_inf] at hn
        obtain ⟨hnX, hnM⟩ := hn
        haveI hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
          rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
        have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) hsetup.E_le,
            hsetup.E_compl_sup, Subgroup.subgroupOf_self]
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hsuptop ▸ Subgroup.mem_top (⟨n, hnM⟩ : ↥M))
        have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
        have he : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
        have hse : (a : G) * (b : G) = n := by
          have h := congrArg (Subtype.val) hab; simpa using h
        -- A nonidentity `g ∈ X` and `y' = e g e⁻¹ ∈ E#`.
        obtain ⟨⟨g, hgX⟩, hg1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hXrank)
        have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
        have hgE : g ∈ E := (hXK.trans hKEeq.le) hgX
        have hy'E : (b : G) * g * (b : G)⁻¹ ∈ E := E.mul_mem (E.mul_mem he hgE) (E.inv_mem he)
        have hy'1 : (b : G) * g * (b : G)⁻¹ ≠ 1 := by
          rw [show (b : G) * g * (b : G)⁻¹ = MulAut.conj (b : G) g from (MulAut.conj_apply _ _).symm]
          exact fun hc => hg1' ((MulAut.conj (b : G)).map_eq_one_iff.mp hc)
        -- `s · y' · s⁻¹ = n g n⁻¹ ∈ X ≤ E`.
        have hsy' : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ = n * g * n⁻¹ := by
          rw [← hse]; group
        have hngn : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnX g).mp hgX
        -- `[s, y'] ∈ M_σ ∩ E = 1`, so `s` centralizes `y'`.
        have hsy'E : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ ∈ E :=
          hsy' ▸ (hXK.trans hKEeq.le) hngn
        have hy'N : (b : G) * g * (b : G)⁻¹ ∈
            Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
          le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M (hsetup.E_le hy'E)
        have hcommMσ : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have h1 : ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹)⁻¹ ∈
              OddOrder.BG.Ch3.S10.Msigma M :=
            (Subgroup.mem_normalizer_iff.mp hy'N (a : G)⁻¹).mp
              ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem hs)
          have heq : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
              ((b : G) * g * (b : G)⁻¹)⁻¹ =
              (a : G) * (((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
                ((b : G) * g * (b : G)⁻¹)⁻¹) := by group
          rw [heq]; exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hs h1
        have hcomm1 : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ = 1 := by
          have hmem : _ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ E :=
            Subgroup.mem_inf.mpr ⟨hcommMσ, E.mul_mem hsy'E (E.inv_mem hy'E)⟩
          rw [hsetup.E_compl_inf] at hmem; exact Subgroup.mem_bot.mp hmem
        -- `s ∈ C_{M_σ}(y') = C_{M_σ}(E) = K*`, `e ∈ E = K`, so `n = s·e ∈ K ⊔ K*`.
        have hscent : (a : G) ∈ Subgroup.centralizer ({(b : G) * g * (b : G)⁻¹} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff.mp hz]
          exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm1)).symm
        have hsKstar : (a : G) ∈ Kstar := by
          rw [hKstar, hKEeq, ← fixedBy_def, ← hEprime _ hy'E hy'1, fixedByElement_def]
          exact Subgroup.mem_inf.mpr ⟨hs, hscent⟩
        rw [← hse]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hsKstar)
          (Subgroup.mem_sup_left (hKEeq ▸ he))
      · refine sup_le ?_ ?_
        · rw [hKEeq]
          exact le_inf (hEnorm p hp X hXrank (hXK.trans hKEeq.le)) (hKEeq ▸ hKM)
        · rw [hKstar]
          exact le_inf
            (inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
              (Subgroup.centralizer_le_normalizer _)))
            (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    · -- (d) `K^* ∩ M^g = 1` for `g ∉ M`: a rank-one `X ≤ K^* ∩ M^g` has `C_G(X) ⊆ M` by (c),
      -- and `X ≤ M^g` with Theorem 10.1(e) forces `g ∈ M`.
      intro g hgM
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ :=
        (Nat.card ↥(Kstar ⊓ (MulAut.conj g • M))).exists_prime_and_dvd
          (fun hc => hne (Subgroup.card_eq_one.mp hc))
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hXcard : Nat.card ↥(Subgroup.zpowers (w : G)) = q := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective _ (Kstar ⊓ (MulAut.conj g • M)).subtype_injective w).trans hw
      have hXelem : Subgroup.zpowers (w : G) ∈ elemAbelianOfRank G q 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
      have hXle : Subgroup.zpowers (w : G) ≤ Kstar ⊓ (MulAut.conj g • M) :=
        Subgroup.zpowers_le.mpr w.2
      have hKstarE : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) := by
        rw [hKstar, hKEeq]
      have hXK : Subgroup.zpowers (w : G) ≤
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) :=
        hKstarE ▸ (hXle.trans inf_le_left)
      -- (c): `C_G(X) ⊆ M`.
      have h𝓜 := maximalContaining_centralizer_of_le_Msigma_centralizer_E hG hsetup hE1ne hXelem hXK
      have hCM : Subgroup.centralizer ((Subgroup.zpowers (w : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      -- `X ≤ M_σ ≤ M`, `q ∈ σ(M)`, `X` a `q`-group.
      have hXMσ : Subgroup.zpowers (w : G) ≤ OddOrder.BG.Ch3.S10.Msigma M := hXK.trans inf_le_left
      have hXM : Subgroup.zpowers (w : G) ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
      have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
          ⟨hq, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
      have hXbot : Subgroup.zpowers (w : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
      have hXp : IsPGroup q ↥(Subgroup.zpowers (w : G)) := hXelem.1.isPGroup
      -- `X ≤ M^g` gives `conj g⁻¹ • X ≤ M`; Theorem 10.1(e) yields `g⁻¹ ∈ M`.
      have hXgM : Subgroup.zpowers (w : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
      have hconj : MulAut.conj g⁻¹ • Subgroup.zpowers (w : G) ≤ M := by
        have h1 : MulAut.conj g⁻¹ • Subgroup.zpowers (w : G) ≤
            MulAut.conj g⁻¹ • (MulAut.conj g • M) :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr hXgM
        rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
      have hg' : g⁻¹ ∈ M :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hqσ hXbot hXp).2.2.2.2
          hXM hCM g⁻¹ hconj
      exact hgM (by simpa using M.inv_mem hg')
    · -- (g) In the `κ ∩ τ₃` case `K = E`, so `κ(M) = π(M) ∖ σ(M)`, i.e. `M` is type `P₁`;
      -- this contradicts `IsTypeP2 M` (whose defining clause is `κ(M) ≠ π(M) ∖ σ(M)`).
      intro hP2
      refine absurd ?_ hP2.2
      apply Set.eq_of_subset_of_subset
      · -- `κ(M) ⊆ π(M) ∖ σ(M)`: each `p ∈ κ` is a prime dividing `|M|` (witness `P ≤ M`) and `∉ σ`.
        intro p hpκ
        obtain ⟨hpp, hpτ, P, hPelem, hPM, _⟩ := hpκ
        have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
        have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := by
          rcases hpτ with h | h
          · exact tau1_subset_sigma_compl M h
          · exact tau3_subset_sigma_compl M h
        exact ⟨Nat.mem_primeFactors.mpr
            ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩, hpσ⟩
      · -- `π(M) ∖ σ(M) ⊆ κ(M)`: `p ∣ |M|`, `p ∉ σ` ⟹ `p ∣ |E|` ⟹ `p ∈ κ` (by `mem_kappa…`).
        intro p hp
        obtain ⟨hpπ, hpσ⟩ := hp
        obtain ⟨hpp, hpdvdM, _⟩ := Nat.mem_primeFactors.mp hpπ
        haveI : Fact p.Prime := ⟨hpp⟩
        have hpnMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
          hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
            (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩))
        have hdvdME : p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
          rw [hsetup.card_Msigma_mul_card_E]; exact hpdvdM
        have hpE : p ∈ (Nat.card ↥E).primeFactors :=
          Nat.mem_primeFactors.mpr
            ⟨hpp, (hpp.dvd_mul.mp hdvdME).resolve_left hpnMσ, Nat.card_pos.ne'⟩
        exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hpE
    · -- (c) `ℳ(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`: `K* = C_{M_σ}(K) = C_{M_σ}(E)` (`K = E`),
      -- so the `C(E)`-form Corollary 12.14 helper (`…_centralizer_E`) applies directly.
      intro p hp X hXelem hXKstar
      haveI : Fact p.Prime := ⟨hp⟩
      exact maximalContaining_centralizer_of_le_Msigma_centralizer_E hG hsetup hE1ne hXelem
        (hKEeq ▸ hKstar ▸ hXKstar)
    · -- (e-core) `K* ⊊ M_σ` (BG Prop 14.2(e)): apply `kstar_ne_msigma_aux` with `E₁ ≤ K = E`.
      have hE1K : E₁ ≤ K := by rw [hKEeq]; exact hsetup.E₁_le
      have hKstar_ne : Kstar ≠ ⊥ := by
        rw [hKstar, hKEeq]
        exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hEprime hsetup.E₃_le hreg
      refine kstar_ne_msigma_aux hG hsetup hE1K (le_of_eq hKEeq) hE1ne
        (fun hKbot => hE1ne (le_bot_iff.mp (hE1K.trans hKbot.le))) (fun q hq => ?_) hKstar hKstar_ne
      exact kappa_subset_tau1_union_tau3 (hK.1 q (by
        rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))
  · -- Case `κ(M) ⊆ τ₁(M)`: `κ = τ₁`, and `K` is `M`-conjugate to `E₁` (both Hall `κ(M)`).
    -- Conjugate the `E`-setup by `w` (`conj w • E₁ = K`) and read the conjuncts off the new setup
    -- via the `E₁`-lemmas (Theorem 13.5 etc.), exactly as in case `τ₃` with `E₁` in place of `E`.
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    -- `E₁ ≠ 1`, non-regular, prime on `M_σ`, `C_{M_σ}(E₁) ≠ 1`.
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    -- `E₁` is a Hall `κ(M)`-subgroup of `E` (π(E₁) ⊆ κ by coverage; index avoids `κ ⊆ τ₁`).
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    -- WLOG `conj w • E₁ = K`; conjugate the setup so its new `E₁` is `K`.
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    -- Read off `K = (h').E₁` facts.
    obtain ⟨hKne, hKnonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hKprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K := E1_actsPrime hG h' hKne
    refine ⟨hKprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (K* ≠ 1) `= C_{M_σ}(K) ≠ 1`.
      rw [hKstar]
      exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
    · -- (b1) `N_M(X) = K ⊔ K*` for rank-one `X ≤ K`.  Here `K = E₁' ⊊ E'`, so the case-`τ₃`
      -- argument is twisted: decompose `n = a·b` (`a ∈ M_σ`, `b ∈ E'`); `[a, bgb⁻¹] = 1` gives
      -- `ngn⁻¹ = bgb⁻¹`, so `s' := b⁻¹n` centralizes `g`, hence `s' ∈ C_{M_σ}(K) = K*` (prime
      -- action), `n = b·s'`, and `b = n·s'⁻¹ ∈ N_G(X) ⊓ E' ≤ K` by the Frobenius normalizer lemma.
      intro p hp X hXrank hXK
      haveI : Fact p.Prime := ⟨hp⟩
      have hKstar_ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hKcentX : K ≤ Subgroup.centralizer (X : Set G) := by
        letI : CommGroup ↥K := (subgroupE_basic hG h').2.2.2.1.1.commGroup
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (mul_comm (⟨y, hXK hy⟩ : ↥K) (⟨k, hk⟩ : ↥K))
      refine le_antisymm ?_ ?_
      · -- ⊆
        intro n hn
        rw [Subgroup.mem_inf] at hn
        obtain ⟨hnX, hnM⟩ := hn
        haveI hMσnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
          rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
        have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔
            (MulAut.conj w • E).subgroupOf M = ⊤ := by
          rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) h'.E_le,
            h'.E_compl_sup, Subgroup.subgroupOf_self]
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
          (hsuptop ▸ Subgroup.mem_top (⟨n, hnM⟩ : ↥M))
        have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
        have he : (b : G) ∈ MulAut.conj w • E := Subgroup.mem_subgroupOf.mp hb
        have hbM : (b : G) ∈ M := h'.E_le he
        have hse : (a : G) * (b : G) = n := by have hh := congrArg Subtype.val hab; simpa using hh
        obtain ⟨⟨g, hgX⟩, hg1⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp (ne_bot_of_mem_elemAbelianOfRank_one hXrank)
        have hg1' : g ≠ 1 := fun hc => hg1 (Subtype.ext hc)
        have hgK : g ∈ K := hXK hgX
        have hgE' : g ∈ MulAut.conj w • E := h'.E₁_le hgK
        have hy'E : (b : G) * g * (b : G)⁻¹ ∈ MulAut.conj w • E :=
          (MulAut.conj w • E).mul_mem ((MulAut.conj w • E).mul_mem he hgE')
            ((MulAut.conj w • E).inv_mem he)
        have hngn : n * g * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hnX g).mp hgX
        have hsy' : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ = n * g * n⁻¹ := by
          rw [← hse]; group
        have hsy'E : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ ∈ MulAut.conj w • E :=
          hsy' ▸ (hXK.trans h'.E₁_le) hngn
        have hy'N : (b : G) * g * (b : G)⁻¹ ∈
            Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
          le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M (h'.E_le hy'E)
        have hcommMσ : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have h1 : ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹)⁻¹ ∈
              OddOrder.BG.Ch3.S10.Msigma M :=
            (Subgroup.mem_normalizer_iff.mp hy'N (a : G)⁻¹).mp
              ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem hs)
          have heq : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
              ((b : G) * g * (b : G)⁻¹)⁻¹ =
              (a : G) * (((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
                ((b : G) * g * (b : G)⁻¹)⁻¹) := by group
          rw [heq]; exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hs h1
        have hcomm1 : (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹ *
            ((b : G) * g * (b : G)⁻¹)⁻¹ = 1 := by
          have hmem : _ ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj w • E) :=
            Subgroup.mem_inf.mpr ⟨hcommMσ, (MulAut.conj w • E).mul_mem hsy'E
              ((MulAut.conj w • E).inv_mem hy'E)⟩
          rw [h'.E_compl_inf] at hmem; exact Subgroup.mem_bot.mp hmem
        -- `n g n⁻¹ = b g b⁻¹` (the `M_σ`-part `a` centralizes `b g b⁻¹`).
        have hngn_eq : n * g * n⁻¹ = (b : G) * g * (b : G)⁻¹ :=
          hsy'.symm.trans (mul_inv_eq_one.mp hcomm1)
        -- `s' := b⁻¹ · n ∈ M_σ` centralizes `g`, so `s' ∈ C_{M_σ}(K) = K*`.
        have hs'Mσ : (b : G)⁻¹ * n ∈ OddOrder.BG.Ch3.S10.Msigma M := by
          have hbinvN : (b : G)⁻¹ ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
            Subgroup.inv_mem _ (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hbM)
          have heq2 : (b : G)⁻¹ * n = (b : G)⁻¹ * (a : G) * ((b : G)⁻¹)⁻¹ := by rw [← hse]; group
          rw [heq2]
          exact (Subgroup.mem_normalizer_iff.mp hbinvN (a : G)).mp hs
        have hs'cent : (b : G)⁻¹ * n ∈ Subgroup.centralizer ({g} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz; rw [Set.mem_singleton_iff.mp hz]
          -- `g * (b⁻¹n) = (b⁻¹n) * g`, i.e. `b⁻¹ n centralizes g`, from `ngn⁻¹ = bgb⁻¹`.
          have hkey : (b : G)⁻¹ * n * g * ((b : G)⁻¹ * n)⁻¹ = g := by
            have hrw : (b : G)⁻¹ * n * g * ((b : G)⁻¹ * n)⁻¹
                = (b : G)⁻¹ * (n * g * n⁻¹) * (b : G) := by group
            rw [hrw, hngn_eq]; group
          exact (mul_inv_eq_iff_eq_mul.mp hkey).symm
        have hs'Kstar : (b : G)⁻¹ * n ∈ Kstar := by
          rw [hKstar, ← fixedBy_def, ← hKprime g hgK hg1', fixedByElement_def]
          exact Subgroup.mem_inf.mpr ⟨hs'Mσ, hs'cent⟩
        -- `b = n · s'⁻¹ ∈ N_G(X) ⊓ E' ≤ K`.
        have hbN : (b : G) ∈ Subgroup.normalizer (X : Set G) := by
          have hs'N : ((b : G)⁻¹ * n)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
            (Subgroup.normalizer (X : Set G)).inv_mem
              ((hKstar ▸ inf_le_right.trans
                ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
                  (Subgroup.centralizer_le_normalizer _))) hs'Kstar)
          have hbeq : (b : G) = n * ((b : G)⁻¹ * n)⁻¹ := by group
          rw [hbeq]; exact (Subgroup.normalizer (X : Set G)).mul_mem hnX hs'N
        have hbK : (b : G) ∈ K :=
          normalizer_inf_E_le_E1_of_caseTau1 hG h' hKne hKstar_ne hτ3 hXrank hXK
            (Subgroup.mem_inf.mpr ⟨hbN, he⟩)
        -- `n = b · s' ∈ K ⊔ K*`.
        have hnbs' : n = (b : G) * ((b : G)⁻¹ * n) := by group
        rw [hnbs']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbK) (Subgroup.mem_sup_right hs'Kstar)
      · refine sup_le (le_inf (hKcentX.trans (Subgroup.centralizer_le_normalizer _)) hKM) ?_
        rw [hKstar]
        exact le_inf
          (inf_le_right.trans ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK)).trans
            (Subgroup.centralizer_le_normalizer _)))
          (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
    · -- (d) `K* ∩ M^g = 1` for `g ∉ M` (mirror of case `τ₃`, using the new setup `h'` whose
      -- `E₁ = K` and the `C(E₁)`-form of (c)).
      intro g hgM
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ :=
        (Nat.card ↥(Kstar ⊓ (MulAut.conj g • M))).exists_prime_and_dvd
          (fun hc => hne (Subgroup.card_eq_one.mp hc))
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨w', hw'⟩ := exists_prime_orderOf_dvd_card' q hqdvd
      have hXcard : Nat.card ↥(Subgroup.zpowers (w' : G)) = q := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective _ (Kstar ⊓ (MulAut.conj g • M)).subtype_injective w').trans hw'
      have hXelem : Subgroup.zpowers (w' : G) ∈ elemAbelianOfRank G q 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
      have hXle : Subgroup.zpowers (w' : G) ≤ Kstar ⊓ (MulAut.conj g • M) :=
        Subgroup.zpowers_le.mpr w'.2
      have hXC : Subgroup.zpowers (w' : G) ≤
          OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) :=
        hKstar ▸ (hXle.trans inf_le_left)
      have h𝓜 := maximalContaining_centralizer_of_le_Msigma_centralizer_E1 hG h' hKne hXelem hXC
      have hCM : Subgroup.centralizer ((Subgroup.zpowers (w' : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      have hXMσ : Subgroup.zpowers (w' : G) ≤ OddOrder.BG.Ch3.S10.Msigma M := hXC.trans inf_le_left
      have hXM : Subgroup.zpowers (w' : G) ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
      have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
          ⟨hq, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
      have hXbot : Subgroup.zpowers (w' : G) ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
      have hXp : IsPGroup q ↥(Subgroup.zpowers (w' : G)) := hXelem.1.isPGroup
      have hXgM : Subgroup.zpowers (w' : G) ≤ MulAut.conj g • M := hXle.trans inf_le_right
      have hconj : MulAut.conj g⁻¹ • Subgroup.zpowers (w' : G) ≤ M := by
        have h1 : MulAut.conj g⁻¹ • Subgroup.zpowers (w' : G) ≤
            MulAut.conj g⁻¹ • (MulAut.conj g • M) :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g⁻¹)).mpr hXgM
        rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
      have hg' : g⁻¹ ∈ M :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hqσ hXbot hXp).2.2.2.2
          hXM hCM g⁻¹ hconj
      exact hgM (by simpa using M.inv_mem hg')
    · -- (g) type-`P₂` ⟹ `σ = β`, `|K|` prime, `M_σ` nilpotent TI.  `IsTypeP2 M` forces
      -- `U = E₂E₃ ≠ 1` (`E23_ne_bot_of_isTypeP2_caseTau1`); the Frobenius core
      -- (`sigma_eq_beta_and_prime_card_E1_of_caseTau1`) gives `σ = β` and `|K|` prime via
      -- Theorem 3.10(a); the TI clause follows from `σ = β` (`isTISubset_sigmaSharp_of_sigma_eq_beta`).
      intro hP2
      have hKstar_ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hUne := E23_ne_bot_of_isTypeP2_caseTau1 hG h' hKprime hKstar_ne hτ3 hP2
      obtain ⟨hσβ, q, hq, hqcard⟩ :=
        sigma_eq_beta_and_prime_card_E1_of_caseTau1 hG h' hKne hKstar_ne hτ3 hUne
      exact ⟨hσβ, q, hq, hqcard, isTISubset_sigmaSharp_of_sigma_eq_beta hG hM hσβ⟩
    · -- (c) `ℳ(C_G(X)) = {M}` for `X ∈ ℰ¹(K*)`: `K* = C_{M_σ}(K) = C_{M_σ}(E₁')` (`K = E₁'`),
      -- so the `C(E₁)`-form Corollary 12.14 helper (`…_centralizer_E1`) applies directly.
      intro p hp X hXelem hXKstar
      haveI : Fact p.Prime := ⟨hp⟩
      exact maximalContaining_centralizer_of_le_Msigma_centralizer_E1 hG h' hKne hXelem
        (hKstar ▸ hXKstar)
    · -- (e-core) `K* ⊊ M_σ` (BG Prop 14.2(e)): apply `kstar_ne_msigma_aux` with `E₁' = K`.
      have hKstar_ne : Kstar ≠ ⊥ := by
        rw [hKstar]
        exact Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      refine kstar_ne_msigma_aux hG h' (le_refl K) h'.E₁_le hKne hKne (fun q hq => ?_) hKstar hKstar_ne
      exact kappa_subset_tau1_union_tau3 (hK.1 q (by
        rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))

/-- **BG Proposition 14.2(b2)** (mmd L3829): for a type-`P` `M`, a Hall `κ(M)`-subgroup `K`, and
`X ∈ ℰ_p¹(K)` with `C_{M_σ}(X) ≠ 1`, every `M* ∈ ℳ(N_G(X))` satisfies `X ⊆ M*_σ`.

This is the clause of Prop 14.2(b) that `typeP_structure` omits — it carries only (b1)
(`N_M(X) = K × K*`).  The hypothesis `C_{M_σ}(X) ≠ 1` is automatic for `X ∈ ℰ¹(K)` (then
`C_{M_σ}(X) ⊇ C_{M_σ}(K) = K* ≠ 1`), so callers supply it from `typeP_structure`'s `K* ≠ 1`.
Theorem 14.7's neighbour analysis (`Z = K×K* ⊆ M_i`, `X_i ⊆ M_{iσ}`) needs this clause.

Proof (BG): `p ∈ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`; Lemma 13.13 (`mem_sigma_of_tau1_tau3_centralize`) gives
`p ∈ σ(M*)`; since `X ≤ N_G(X) ≤ M*` is a `σ(M*)`-subgroup, `X ⊆ M*_σ`. -/
theorem typeP_elemAbelian_le_neighbor_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    X ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
  classical
  -- `p ∈ κ(M) ⊆ τ₁(M) ∪ τ₃(M)`.
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [(mem_elemAbelianOfRank.mp hX).2]; exact dvd_pow_self p one_ne_zero
  have hpcardK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXK), Nat.card_pos.ne'⟩
  have hpκ : p ∈ kappa M := hK.1 p (by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpcardK)
  have hpτ13 : p ∈ tau1 M ∪ tau3 M := kappa_subset_tau1_union_tau3 hpκ
  -- `K` is a `σ(M)'`-subgroup; get an `E`-setup with `K ≤ E`, so `X ≤ E`.
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := fun q hq =>
    kappa_subset_sigmaCompl (hK.1 q (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hq))
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, _⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  -- Lemma 13.13: `p ∈ σ(M*)`.
  have hpσMstar : p ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
    OddOrder.BG.Ch3.S13.mem_sigma_of_tau1_tau3_centralize hG hsetup hpτ13 hX (hXK.trans hKE)
      hCX hMstar
  -- `X ≤ M*` is a `σ(M*)`-subgroup, hence `X ≤ M*_σ`.
  have hMstarMax : Mstar ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMstar).1
  have hXMstar : X ≤ Mstar :=
    Subgroup.le_normalizer.trans (mem_maximalSubgroupsContaining.mp hMstar).2
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarMax) hXMstar (fun q hq => ?_)
  rw [(mem_elemAbelianOfRank.mp hX).2, pow_one, Nat.Prime.primeFactors (Fact.out : p.Prime),
    Finset.mem_singleton] at hq
  rwa [hq]

/-- **Theorem 14.7 neighbour-embedding** (BG L3977-3982), step 1 of the §16-independent
pre-position: for a type-`P` `M` with Hall `κ(M)`-subgroup `K`, `K* = C_{M_σ}(K)`, and
`X ∈ ℰ_p¹(K)` with `C_{M_σ}(X) ≠ 1`, every neighbour `M_i ∈ ℳ(N_G(X))` is **not conjugate to `M`**,
contains `Z = K ⊔ K*`, and has `X ⊆ M_{iσ}`.

Uses Prop 14.2(b1) [`N_M(X) = K×K*`, so `K ⊔ K* = N_G(X) ⊓ M ≤ N_G(X) ≤ M_i`], Prop 14.2(b2)
[`X ⊆ M_{iσ}`], and `σ`-conjugation-invariance: `p ∈ π(X) ⊆ κ(M) ⊆ σ(M)'`, but `X ⊆ M_{iσ}` gives
`p ∈ σ(M_i)`, so `M_i = M^g` would force `p ∈ σ(M^g) = σ(M)`, a contradiction. -/
theorem typeP_neighbor_embed [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ¬ IsConjugateSubgroup M Mi ∧ K ⊔ Kstar ≤ Mi ∧ X ≤ OddOrder.BG.Ch3.S10.Msigma Mi := by
  classical
  -- `p ∈ κ(M)`.
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [(mem_elemAbelianOfRank.mp hX).2]; exact dvd_pow_self p one_ne_zero
  have hpcardK : p ∈ (Nat.card ↥K).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXK), Nat.card_pos.ne'⟩
  have hpκ : p ∈ kappa M := hK.1 p (by
    rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpcardK)
  -- `X ⊆ M_{iσ}` (Prop 14.2(b2)).
  have hXMiσ : X ≤ OddOrder.BG.Ch3.S10.Msigma Mi :=
    typeP_elemAbelian_le_neighbor_Msigma hG hM hKM hK hX hXK hCX hMi
  -- `K ⊔ K* ≤ M_i` (Prop 14.2(b1): `N_G(X) ⊓ M = K ⊔ K*`, and `N_G(X) ≤ M_i`).
  obtain ⟨_, _, hb1, _, _, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hZMi : K ⊔ Kstar ≤ Mi := by
    rw [← hb1 p Fact.out X hX hXK]
    exact le_trans inf_le_left (mem_maximalSubgroupsContaining.mp hMi).2
  refine ⟨?_, hZMi, hXMiσ⟩
  -- `M_i` not conjugate to `M`: else `σ(M_i) = σ(M)`, but `p ∈ σ(M_i) ∩ κ(M) ⊆ σ(M) ∩ σ(M)'`.
  rintro ⟨g, hg⟩
  have hpσMi : p ∈ OddOrder.BG.Ch3.S10.sigma Mi :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi p (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hpdvd.trans (Subgroup.card_dvd_of_le hXMiσ), Nat.card_pos.ne'⟩)
  rw [← hg] at hpσMi
  have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    have h2 := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hpσMi
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  exact kappa_subset_sigmaCompl hpκ hpσM

/-- **A `κ(M)`-subgroup of `M` lies in some Hall `κ(M)`-subgroup of `M`** (Hall D / Wielandt,
`Ch03.hall_D`, applied inside the solvable group `↥M`).  Used by Corollary 14.3 branch 1 to put
the `κ`-witness `X₀ ≤ ⟨x'⟩` into a Hall `κ`-subgroup `K`, so that Proposition 14.2(b1)/(c) apply. -/
theorem exists_isHallSubgroup_kappa_ge [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXκ : ∀ q ∈ (Nat.card ↥X).primeFactors, q ∈ kappa M) :
    ∃ K : Subgroup G, K ≤ M ∧ Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M) ∧ X ≤ K := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hXsub : ∀ q ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hq
    exact hXκ q hq
  obtain ⟨K', hK'hall, hK'ge⟩ := Ch03.hall_D (G := ↥M) hXsub
  have hKeq : (K'.map M.subtype).subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  refine ⟨K'.map M.subtype, Subgroup.map_subtype_le K', ?_, ?_⟩
  · rw [hKeq]; exact hK'hall
  · exact le_of_eq_of_le (Subgroup.map_subgroupOf_eq_of_le hXM).symm (Subgroup.map_mono hK'ge)

/-- **`C_M(M_σ)` is a `κ(M)'`-group** (BG Corollary 15.3 step, mmd L4209 "By Proposition
14.2(b1) and (e), `C_M(H)` is a `κ(M)'`-group", for `H = M_σ`).  No prime of `κ(M)` divides
`|C_M(M_σ)|`.

Proof.  If some `p ∈ κ(M)` divided `|C_M(M_σ)|`, take `x ∈ C_M(M_σ)` of order `p`; then
`X₀ = ⟨x⟩` is a `κ`-subgroup, so it lies in a Hall `κ(M)`-subgroup `K`.  Since `x` centralizes
`M_σ`, `M_σ ≤ C_G(X₀) ≤ N_G(X₀)`, and Proposition 14.2(b1) (`typeP_structure` conjunct 3) gives
`N_G(X₀) ⊓ M = K ⊔ K*`.  By the Dedekind identity (`K* ≤ M_σ`, `M_σ ⊓ K = ⊥`, `K ≤ N(K*)`),
`M_σ ⊓ (K ⊔ K*) = K*`, whence `M_σ = K*`, contradicting `K* ≠ M_σ` (`typeP_structure`
conjunct 7, BG Prop 14.2(e), `kstar_ne_msigma_aux`). -/
theorem centralizer_msigma_isPiSubgroup_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.IsPiSubgroup (kappa M)ᶜ
      (Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpκ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hP : IsTypeP M := ⟨p, hpκ⟩
  -- Cauchy: an order-`p` element `x` of `C = C_M(M_σ)`; `X₀ = ⟨x⟩`.
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hX₀card : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.centralizer _ ⊓ M).subtype_injective x).trans hxord
  have hX₀C : Subgroup.zpowers (x : G) ≤
      Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr x.2
  have hX₀M : Subgroup.zpowers (x : G) ≤ M := hX₀C.trans inf_le_right
  have hX₀elem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX₀card, by rw [hX₀card, pow_one]⟩
  -- `X₀` is a `κ`-subgroup, so it lies in a Hall `κ(M)`-subgroup `K`.
  have hX₀κ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers (x : G))).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [hX₀card, Nat.Prime.primeFactors hpp, Finset.mem_singleton] at hq
    rwa [hq]
  obtain ⟨K, hKM, hKHall, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
  -- A Hall `(κ ∪ σ)'`-subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUof : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUof]; exact hU'
  -- `typeP_structure`: (b1) and (e) `K* ≠ M_σ`, with `K* = M_σ ⊓ C(K)`.
  obtain ⟨_, _, hb1, _, _, _, hKstar_ne⟩ := typeP_structure hG hM hP hKM hKHall
    (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) = _) hUHall
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
  -- `M_σ ≤ N_G(X₀) ⊓ M = K ⊔ K*`  (`X₀ ≤ C(M_σ)` ⟹ `M_σ ≤ C(X₀) ≤ N_G(X₀)`).
  have hMσ_le : OddOrder.BG.Ch3.S10.Msigma M ≤ K ⊔ Kstar := by
    rw [← hb1 p hpp _ hX₀elem hX₀K]
    refine le_inf ?_ (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hcent : OddOrder.BG.Ch3.S10.Msigma M ≤
        Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G) :=
      Subgroup.le_centralizer_iff.mp (hX₀C.trans inf_le_left)
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  -- Dedekind: `M_σ ⊓ (K ⊔ K*) = K*`.
  have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
  have hKnormKstar : K ≤ Subgroup.normalizer (Kstar : Set G) :=
    (Subgroup.le_centralizer_iff.mp (inf_le_right : Kstar ≤ Subgroup.centralizer (K : Set G))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMσK_bot : OddOrder.BG.Ch3.S10.Msigma M ⊓ K = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr) (fun r hr => ?_))
    exact kappa_subset_sigmaCompl (hKHall.1 r (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr))
  have hdedekind : OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) = Kstar := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right K Kstar hKnormKstar,
      ← Subgroup.inf_mul_assoc _ _ _ hKstar_le_Mσ, hMσK_bot, Subgroup.coe_bot]
    simp
  -- `M_σ = K*` (since `M_σ ≤ K ⊔ K*`), contradicting `K* ≠ M_σ`.
  exact hKstar_ne (((inf_of_le_left hMσ_le).symm).trans hdedekind).symm

/-- **§12 `E`-setup adapted to a `κ(M)`-Hall subgroup `K`** (the preamble of BG Prop 14.2's proof,
mmd L3832-3840).  For a type-`P` `M` and a Hall `κ(M)`-subgroup `K`, there is an `E`-setup whose
`τ₁`-Hall `E₁` lies in `K ≤ E` with `E₁ ≠ 1`.  In the `κ ∩ τ₃ ≠ ∅` case `K = E ⊇ E₁`; in the
`κ ⊆ τ₁` case the setup is conjugated so its `E₁` becomes `K`.  Packages exactly the hypotheses
that `typeP_sylow_not_le_kstar` (Prop 14.2(e)) consumes. -/
theorem exists_typePESetup_kappaHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    ∃ E E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ ∧ E₁ ≤ K ∧ K ≤ E ∧ E₁ ≠ ⊥ := by
  classical
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, _⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ ∩ τ₃ ≠ ∅`: `E = E₁ E₃` is `κ`-pure, so `K = E`; then `E₁ ≤ E = K`.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, _, hEprime, _⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    exact ⟨E, E₁, E₂, E₃, hsetup, hsetup.E₁_le.trans hKEeq.ge, hKEeq.le, hE1ne⟩
  · -- Case `κ ⊆ τ₁`: `K` is `M`-conjugate to `E₁`; conjugate the setup so its new `E₁ = K`.
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    obtain ⟨hKne, _⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    exact ⟨MulAut.conj w • E, K, MulAut.conj w • E₂, MulAut.conj w • E₃, h', le_refl K,
      h'.E₁_le, hKne⟩

/-- **BG Proposition 14.2(e), packaged for `typeP_structure` inputs** (mmd L3828).  The `S ⊄ K*`
clause of Prop 14.2(e) stated with the natural type-`P` hypotheses (`M` maximal type-`P`, `K` a
Hall `κ(M)`-subgroup) instead of a raw `E`-setup: it builds the setup via
`exists_typePESetup_kappaHall` and applies `typeP_sylow_not_le_kstar`. -/
theorem typeP_sylow_not_le_kstar_of_isHall [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKstar_ne : Kstar ≠ ⊥)
    {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hSne : S ≠ ⊥)
    (hSle : S ≤ OddOrder.BG.Ch3.S10.Msigma M) (hSq : IsPGroup q ↥S)
    (hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T) :
    ¬ S ≤ Kstar := by
  obtain ⟨E, E₁, E₂, E₃, h, hE1K, hKE, hE1ne⟩ := exists_typePESetup_kappaHall hG hM hP hKM hK
  have hKne : K ≠ ⊥ := fun hKbot => hE1ne (le_bot_iff.mp (hE1K.trans hKbot.le))
  have hKpi13 : ∀ p ∈ (Nat.card ↥K).primeFactors, p ∈ tau1 M ∪ tau3 M := fun p hp =>
    kappa_subset_tau1_union_tau3 (hK.1 p (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp))
  exact typeP_sylow_not_le_kstar hG h hE1K hKE hE1ne hKne hKpi13 hKstar hKstar_ne
    hSne hSle hSq hSmax

/-- **`C_M(H)` is a `κ(M)'`-group for every nontrivial Hall subgroup `H` of `M_σ`** (BG Corollary
15.3(a) start, mmd L4209 "By Proposition 14.2(b1) and (e), `C_M(H)` is a `κ(M)'`-group").  The
general-Hall analogue of `centralizer_msigma_isPiSubgroup_kappa_compl` (`H = M_σ`).

Proof.  If `p ∈ κ(M)` divided `|C_M(H)|`, take `x ∈ C_M(H)` of order `p`; then `X₀ = ⟨x⟩` is a
`κ`-subgroup lying in a Hall `κ(M)`-subgroup `K`.  Since `x` centralizes `H`, `H ≤ C_G(X₀) ≤
N_G(X₀)`, and Prop 14.2(b1) gives `N_G(X₀) ⊓ M = K ⊔ K*`; with `H ≤ M_σ`, the Dedekind identity
`M_σ ⊓ (K ⊔ K*) = K*` forces `H ≤ K*`.  As `H` is Hall in `M_σ`, a Sylow `q`-subgroup `S` of `M_σ`
(for `q ∈ π(H)`) lies in `H ≤ K*`, contradicting Prop 14.2(e)
(`typeP_sylow_not_le_kstar_of_isHall`, `S ⊄ K*`). -/
theorem centralizer_hall_isPiSubgroup_kappa_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hHhall : Ch03.IsHallSubgroup (piSet H) (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hHne : H ≠ ⊥) :
    Subgroup.IsPiSubgroup (kappa M)ᶜ (Subgroup.centralizer (H : Set G) ⊓ M) := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpκ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hP : IsTypeP M := ⟨p, hpκ⟩
  -- Cauchy: `x ∈ C = C_G(H) ⊓ M` of order `p`; `X₀ = ⟨x⟩`.
  have hpdvd : p ∣ Nat.card ↥(Subgroup.centralizer (H : Set G) ⊓ M) :=
    (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hX₀card : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.centralizer _ ⊓ M).subtype_injective x).trans hxord
  have hX₀C : Subgroup.zpowers (x : G) ≤ Subgroup.centralizer (H : Set G) ⊓ M :=
    Subgroup.zpowers_le.mpr x.2
  have hX₀M : Subgroup.zpowers (x : G) ≤ M := hX₀C.trans inf_le_right
  have hX₀elem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX₀card, by rw [hX₀card, pow_one]⟩
  have hX₀κ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers (x : G))).primeFactors, q ∈ kappa M := by
    intro q hq
    rw [hX₀card, Nat.Prime.primeFactors hpp, Finset.mem_singleton] at hq
    rwa [hq]
  obtain ⟨K, hKM, hKHall, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUof : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUof]; exact hU'
  -- `typeP_structure`: `K* ≠ 1` and (b1) `N_M(X₀) = K ⊔ K*`.
  obtain ⟨_, hKstar_ne, hb1, _, _, _, _⟩ := typeP_structure hG hM hP hKM hKHall
    (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) = _) hUHall
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
  -- `H ≤ C_G(X₀) ≤ N_G(X₀)` (`x` centralizes `H`), and `H ≤ M`, so `H ≤ N_M(X₀) = K ⊔ K*`.
  have hH_le_N : H ≤ Subgroup.normalizer ((Subgroup.zpowers (x : G)) : Set G) :=
    (Subgroup.le_centralizer_iff.mp (hX₀C.trans inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hH_le_KKstar : H ≤ K ⊔ Kstar := by
    rw [← hb1 p hpp _ hX₀elem hX₀K]
    exact le_inf hH_le_N (hHMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  -- Dedekind: `M_σ ⊓ (K ⊔ K*) = K*`; with `H ≤ M_σ`, `H ≤ K*`.
  have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
  have hKnormKstar : K ≤ Subgroup.normalizer (Kstar : Set G) :=
    (Subgroup.le_centralizer_iff.mp
      (inf_le_right : Kstar ≤ Subgroup.centralizer (K : Set G))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hMσK_bot : OddOrder.BG.Ch3.S10.Msigma M ⊓ K = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr) (fun r hr => ?_))
    exact kappa_subset_sigmaCompl (hKHall.1 r (by
      rwa [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hr))
  have hdedekind : OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) = Kstar := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right K Kstar hKnormKstar,
      ← Subgroup.inf_mul_assoc _ _ _ hKstar_le_Mσ, hMσK_bot, Subgroup.coe_bot]
    simp
  have hH_le_Kstar : H ≤ Kstar := by
    have hHmem : H ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ (K ⊔ Kstar) := le_inf hHMσ hH_le_KKstar
    rwa [hdedekind] at hHmem
  -- A prime `q ∈ π(H)` and a Sylow `q`-subgroup `S` of `M_σ` with `S ≤ H ≤ K*`.
  obtain ⟨q, hq, hqdvd⟩ := (Nat.card ↥H).exists_prime_and_dvd
    (fun hc => hHne (Subgroup.card_eq_one.mp hc))
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow q ↥H) := Sylow.nonempty
  set S : Subgroup G := (P : Subgroup ↥H).map H.subtype with hSdef
  have hS_le_H : S ≤ H := hSdef ▸ Subgroup.map_subtype_le _
  have hS_le_Mσ : S ≤ OddOrder.BG.Ch3.S10.Msigma M := hS_le_H.trans hHMσ
  have hScardH : Nat.card ↥S = q ^ (Nat.card ↥H).factorization q := by
    rw [hSdef, Subgroup.card_map_of_injective H.subtype_injective, P.card_eq_multiplicity]
  have hSq : IsPGroup q ↥S := IsPGroup.iff_card.mpr ⟨_, hScardH⟩
  -- Hall: `q ∤ [M_σ : H]`, so `v_q(|H|) = v_q(|M_σ|)`.
  have hqpiH : q ∈ piSet H := Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
  have hHcard : Nat.card ↥(H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHMσ).toEquiv
  have hq_ndvd_index : ¬ q ∣ (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := fun hdvd =>
    hHhall.index_no_pi q
      (Nat.mem_primeFactors.mpr ⟨hq, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqpiH
  have hfact_eq : (Nat.card ↥H).factorization q
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).factorization q := by
    have hsplit : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)
        = Nat.card ↥H * (H.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).index := by
      rw [← hHcard]; exact (Subgroup.card_mul_index _).symm
    rw [hsplit, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hq_ndvd_index, add_zero]
  have hScard : Nat.card ↥S = q ^ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)).factorization q := by
    rw [hScardH, hfact_eq]
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T → S = T :=
    fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hqdvdS : q ∣ Nat.card ↥S := by
      rw [hScardH]
      exact dvd_pow_self q (hq.factorization_pos_of_dvd Nat.card_pos.ne' hqdvd).ne'
    rw [Subgroup.card_eq_one.mpr hSbot] at hqdvdS
    exact hq.one_lt.ne' (Nat.dvd_one.mp hqdvdS)
  exact typeP_sylow_not_le_kstar_of_isHall hG hM hP hKM hKHall hKstardef hKstar_ne
    hSne hS_le_Mσ hSq hSmax (hS_le_H.trans hH_le_Kstar)

/-- **BG Corollary 14.3, branch-2 piece** (mmd L3858): if `x'` is a nonidentity `τ₂(M)`-element
of `M` with `C_{M_σ}(x') ≠ 1`, then `ℳ(C_G(x')) = {M}`.  This is Corollary 12.10(e)
(`nilpotent_sigmaComplement_abelian`, fifth conjunct) for an `E`-setup of `M`, with the prime
set `π(⟨x'⟩)` rewritten as `(orderOf x').primeFactors`. -/
theorem maximalContaining_centralizer_eq_singleton_of_tau2_element [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x' : G} (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'τ2 : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M)
    (hC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M} := by
  classical
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hcard : Nat.card ↥(Subgroup.closure {x'}) = orderOf x' := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  exact (nilpotent_sigmaComplement_abelian hG hsetup).2.2.2.2 x' hx'M hx'1
    (fun r hr => hx'τ2 r (by
      show r ∈ (Nat.card ↥(Subgroup.closure {x'})).primeFactors
      rw [hcard]; exact hr)) hC

/-- **`pi_of_cent_sigma` τ₂-case uniqueness** (Coq `BGsection14`:806, the `'M('C[y]) = [set M]`
half of the τ₂ branch of Corollary 14.3): for `x ∈ M_σ^#` and a `τ₂(M)`-element `x' ∈ (C_M[x])^#`,
the unique maximal subgroup containing `C_G(x')` is `M`.  The nonregularity side condition of
`maximalContaining_centralizer_eq_singleton_of_tau2_element` (`M_σ ⊓ C_G(x') ≠ 1`) is witnessed by
`x`: since `x'` centralizes `x`, `x` centralizes `x'`, and `x ∈ M_σ^#`.  This is the directly
discharged part of `pi_of_cent_sigma`'s τ₂ branch (the `ℓ_σ(x') = 1` part needs
`primes_norm_tau2Elem`, the κ branch needs `Ptype_structure`). -/
theorem pi_of_cent_sigma_tau2_uniqueness [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cx : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'τ2 : ∀ p ∈ piSet (Subgroup.closure ({x'} : Set G)), p ∈ tau2 M) :
    maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M} := by
  have hcomm : x * x' = x' * x :=
    Subgroup.mem_centralizer_iff.mp hx'cx x rfl
  have hxcx' : x ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm.symm
  refine maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM hx'M hx'1 hx'τ2 ?_
  intro hbot
  have hxmem : x ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxMσ, hxcx'⟩
  rw [hbot, Subgroup.mem_bot] at hxmem
  exact hx1 hxmem

/-- **BG Lemma 15.1(c)** (mmd L4170): if `U` is a `(κ(M) ∪ σ(M))'`-Hall subgroup of `M` and
`X` is a nonidentity subgroup of `U` with `C_{M_σ}(X) ≠ 1`, then `ℳ(C_G(X)) = {M}` and `X` is a
cyclic `τ₂(M)`-subgroup.

Proof (following BG L4176): since `X ≤ U`, every prime `p ∈ π(X)` lies in `(κ(M) ∪ σ(M))'`,
so `p ∉ σ(M)`, `p ∉ κ(M)`, and `p ∈ π(M)`.

*`π(X) ⊆ τ₂(M)`:* if some `p ∈ π(X)` had `p ∉ τ₂(M)`, then `r_p(M) = 1`, and a rank-one
elementary abelian `A ≤ X` (Cauchy) realizes the maximal rank, so Lemma 14.1
(`msigma_structure_of_notMem_sigma_kappa`) gives `C_{M_σ}(A) = 1`; centralizer antitonicity
(`A ≤ X`) yields `C_{M_σ}(X) ≤ C_{M_σ}(A) = 1`, contradicting `hCX`.

*`X` cyclic:* `X` is a `τ₂(M)`-subgroup of the solvable `M`, hence (Hall D) conjugate into the
abelian Hall `τ₂(M)`-subgroup `E₂` (Corollary 12.10(b)), so `X` is abelian.  Each Sylow `p` of `X`
is cyclic, for if it contained `A ∈ ℰ_p²(X)` then Theorem 12.5(d) (`Msigma_nilpotent_of_tau2`)
would give `C_{M_σ}(A) = 1` and again `C_{M_σ}(X) = 1`.  An abelian group with cyclic Sylow
subgroups is cyclic (`isCyclic_of_sylow_isCyclic`).

*`ℳ(C_G(X)) = {M}`:* with `X = ⟨x⟩` cyclic and `C_G(X) = C_G(x)`, apply Corollary 14.3 branch 2
(`maximalContaining_centralizer_eq_singleton_of_tau2_element`). -/
theorem typeP_hall_small_subgroup_cyclic_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {X : Subgroup G} (hXU : X ≤ U) (hXne : X ≠ ⊥)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      IsCyclic ↥X ∧ (↑(Nat.card ↥X).primeFactors ⊆ tau2 M) := by
  classical
  haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  have hXM : X ≤ M := hXU.trans hUM
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  -- Each prime of `X` lies in `(κ(M) ∪ σ(M))'`, hence `∉ σ`, `∉ κ`, and `∈ π(M)`.
  have hXprimes : ∀ p ∈ (Nat.card ↥X).primeFactors,
      p ∉ OddOrder.BG.Ch3.S10.sigma M ∧ p ∉ kappa M ∧ p ∈ piSet M := by
    intro p hp
    obtain ⟨hpp, hpdvdX, _⟩ := Nat.mem_primeFactors.mp hp
    have hpdvdU : p ∣ Nat.card ↥U := hpdvdX.trans (Subgroup.card_dvd_of_le hXU)
    have hpdvdM : p ∣ Nat.card ↥M := hpdvdX.trans (Subgroup.card_dvd_of_le hXM)
    have hpUM : p ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpdvdU, Nat.card_pos.ne'⟩
    have hpcompl : p ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := hU.1 p hpUM
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpcompl
    exact ⟨hpcompl.2, hpcompl.1, Nat.mem_primeFactors.mpr ⟨hpp, hpdvdM, Nat.card_pos.ne'⟩⟩
  -- **Part A**: `π(X) ⊆ τ₂(M)`.
  have hXτ2 : ∀ p ∈ (Nat.card ↥X).primeFactors, p ∈ tau2 M := by
    intro p hp
    obtain ⟨hpσ, hpκ, hpπ⟩ := hXprimes p hp
    obtain ⟨hpp, hpdvdX, _⟩ := Nat.mem_primeFactors.mp hp
    haveI : Fact p.Prime := ⟨hpp⟩
    by_contra hpτ2
    -- `p ∉ τ₂(M)` with `p ∉ σ(M)` gives `r_p(M) ≠ 2`; rank bounds force `r_p(M) = 1`.
    have hr2 : pRank ↥M p ≠ 2 := fun h => hpτ2 ((mem_tau2_iff M p).mpr ⟨hpσ, h⟩)
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      mem_primeFactors_E_of_mem_M_of_not_sigma hG hsetup hpp hpπ hpσ
    have h1r : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpπ
    have hub : pRank ↥M p ≤ 2 := hsetup.pRank_M_le_two hG hpE
    have hr1 : pRank ↥M p = 1 := by omega
    -- A rank-one elementary abelian subgroup `A ≤ X` of maximal rank.
    obtain ⟨a, hacard⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpdvdX
    set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
    have hAX : A ≤ X := by rw [hAdef, Subgroup.zpowers_le]; exact a.2
    have haGcard : orderOf (a : G) = p :=
      (orderOf_injective X.subtype X.subtype_injective a).trans hacard
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact haGcard
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hA : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]
      exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    -- Lemma 14.1: `C_{M_σ}(A) = 1`; antitonicity gives `C_{M_σ}(X) = 1`, contradiction.
    obtain ⟨_, hCA, _⟩ :=
      msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hA (hAX.trans hXM)
    apply hCX
    rw [eq_bot_iff, ← hCA]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAX))
  -- **Part B(i)**: `X` is abelian (conjugate into the abelian Hall `τ₂`-subgroup `E₂`).
  -- `X` is a `τ₂(M)`-subgroup, so `X.subgroupOf M` is a `τ₂(M)`-π-subgroup of `↥M`.
  have hXsub : ∀ q ∈ (Nat.card ↥(X.subgroupOf M)).primeFactors, q ∈ tau2 M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv] at hq
    exact hXτ2 q hq
  obtain ⟨H', hH'hall, hH'ge⟩ := Ch03.hall_D (G := ↥M) hXsub
  set HG : Subgroup G := H'.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup (tau2 M) (HG.subgroupOf M) := by
    rw [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hH'hall
  have hX_le_HG : X ≤ HG := by
    rw [hHGdef]
    refine le_trans ?_ (Subgroup.map_mono hH'ge)
    rw [Subgroup.map_subgroupOf_eq_of_le hXM]
  -- `E₂` is also a Hall `τ₂(M)`-subgroup of `M`.
  have hE₂_hall_M : Ch03.IsHallSubgroup (tau2 M) (E₂.subgroupOf M) :=
    hallPiece_isHall_in_M hG hsetup hsetup.E₂_le hsetup.E₂_hall (tau2_subset_sigma_compl M)
  -- Conjugate `HG` onto `E₂` (Hall C inside `↥M`).
  obtain ⟨w, _, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv hHG_le_M hsetup.E2_le_M
      hHG_hall hE₂_hall_M
  have hbE₂ : IsMulCommutative ↥E₂ := (nilpotent_sigmaComplement_abelian hG hsetup).2.1.1
  -- `conj w • X ≤ E₂`; commuting in `E₂` transports back to `X`.
  have hXwE₂ : (MulAut.conj w • X : Subgroup G) ≤ E₂ := by
    rw [← hw]
    exact Subgroup.map_mono hX_le_HG
  have hXab : IsMulCommutative ↥X := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    -- `w·a·w⁻¹` and `w·b·w⁻¹` lie in `conj w • X ≤ E₂`, hence commute.
    have haw : w * (a : G) * w⁻¹ ∈ E₂ := by
      apply hXwE₂
      have h := (Subgroup.smul_mem_pointwise_smul_iff
        (a := MulAut.conj w) (S := X) (x := (a : G))).mpr a.2
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have hbw : w * (b : G) * w⁻¹ ∈ E₂ := by
      apply hXwE₂
      have h := (Subgroup.smul_mem_pointwise_smul_iff
        (a := MulAut.conj w) (S := X) (x := (b : G))).mpr b.2
      rwa [MulAut.smul_def, MulAut.conj_apply] at h
    have hcomm : (w * (a : G) * w⁻¹) * (w * (b : G) * w⁻¹)
        = (w * (b : G) * w⁻¹) * (w * (a : G) * w⁻¹) :=
      congrArg Subtype.val (hbE₂.is_comm.comm ⟨_, haw⟩ ⟨_, hbw⟩)
    have hcancel := congrArg (fun u => w⁻¹ * u * w) hcomm
    simpa [mul_assoc] using hcancel
  haveI : IsMulCommutative ↥X := hXab
  -- **Part B(ii)**: every Sylow `p` of `X` is cyclic (else `ℰ_p²(X)` ↝ `C_{M_σ}(X) = 1`).
  have hSylcyc : ∀ p : ℕ, p.Prime → ∀ P : Sylow p ↥X, IsCyclic P := by
    intro p hp P
    haveI : Fact p.Prime := ⟨hp⟩
    by_contra hPnc
    -- `P` is noncyclic, hence nontrivial, so `p ∣ |X|` and (oddness of `G`) `p` is odd.
    have hpcardP : p ∣ Nat.card ↥(P : Subgroup ↥X) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · refine absurd ?_ hPnc
        haveI : Subsingleton ↥(P : Subgroup ↥X) :=
          (Nat.card_eq_one_iff_unique.mp (by rw [hn, h0, pow_zero])).1
        exact isCyclic_of_subsingleton
      · rw [hn]; exact dvd_pow_self p hpos.ne'
    have hpcardX : p ∣ Nat.card ↥X :=
      hpcardP.trans (Subgroup.card_subgroup_dvd_card _)
    have hodd : Odd p :=
      hG.odd.of_dvd_nat (hpcardX.trans (Subgroup.card_subgroup_dvd_card X))
    -- A noncyclic odd `p`-group contains a rank-two elementary abelian subgroup (BG Lemma 4.5(a)).
    obtain ⟨B, hBelem, hBcard⟩ :=
      OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
        P.isPGroup' hodd hPnc
    -- Map `B ≤ P ≤ ↥X` up to `G`.
    set A : Subgroup G := (B.map (P : Subgroup ↥X).subtype).map X.subtype with hAdef
    have hAelem : A.IsElementaryAbelian p := by
      rw [hAdef]
      exact (hBelem.map (Subgroup.subtype_injective _)).map X.subtype_injective
    have hAcard : Nat.card ↥A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBcard]
    have hAX : A ≤ X := by
      rw [hAdef]
      exact le_trans (Subgroup.map_mono (Subgroup.map_subtype_le _)) (Subgroup.map_subtype_le _)
    have hA2 : A ∈ elemAbelianOfRank G p 2 := mem_elemAbelianOfRank.mpr ⟨hAelem, hAcard⟩
    -- `p ∈ τ₂(M)`, then Theorem 12.5(d): `C_{M_σ}(A) = 1`, contradicting `hCX`.
    have hpX : p ∈ (Nat.card ↥X).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Nat.card_pos.ne'⟩
      exact (dvd_pow_self p two_ne_zero).trans (hAcard ▸ Subgroup.card_dvd_of_le hAX)
    have hpτ2 : p ∈ tau2 M := hXτ2 p hpX
    have hCA := (Msigma_nilpotent_of_tau2 hG hM hpτ2 hA2 (hAX.trans hXM)).2.2.2.1
    apply hCX
    rw [eq_bot_iff, ← hCA]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAX))
  -- `X` abelian with cyclic Sylows ⟹ `X` cyclic.
  have hXcyc : IsCyclic ↥X := by
    letI : IsMulCommutative ↥X := hXab
    exact OddOrder.Isaacs.Ch06.isCyclic_of_sylow_isCyclic hSylcyc
  refine ⟨?_, hXcyc, fun p hp => hXτ2 p hp⟩
  -- **Part C**: `ℳ(C_G(X)) = {M}` via the cyclic generator `x`.
  obtain ⟨x₀, hx₀gen⟩ := hXcyc.exists_generator
  set x : G := (x₀ : G) with hxdef
  have hXeq : X = Subgroup.zpowers x := by
    apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx₀gen ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [hxdef, ← Subgroup.coe_zpow, hk]
    · rw [Subgroup.zpowers_le, hxdef]; exact x₀.2
  have hxX : x ∈ X := hXeq ▸ Subgroup.mem_zpowers x
  have hxM : x ∈ M := hXM hxX
  -- `x ≠ 1` (else `X = ⟨1⟩ = ⊥`).
  have hx1 : x ≠ 1 := by
    intro hxe
    apply hXne
    rw [hXeq, hxe, Subgroup.zpowers_one_eq_bot]
  -- `π(⟨x⟩) ⊆ τ₂(M)`.
  have hxτ2 : ∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 M := by
    intro p hp
    refine hXτ2 p ?_
    have : Subgroup.closure {x} = X := by rw [← Subgroup.zpowers_eq_closure, ← hXeq]
    rwa [this] at hp
  -- `C_G(X) = C_G({x})`.
  have hCeq : Subgroup.centralizer (X : Set G) = Subgroup.centralizer ({x} : Set G) := by
    rw [hXeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    rwa [hCeq] at hCX
  rw [hCeq]
  exact maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM hxM hx1 hxτ2 hCne

/-- The `σ`-set is conjugation-invariant: `σ(Mᵍ) = σ(M)` (both inclusions from `sigma_conj`;
non-primes lie in neither set). -/
theorem sigma_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.sigma (MulAut.conj g • M) = OddOrder.BG.Ch3.S10.sigma M := by
  ext p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    refine ⟨fun hmem => ?_, fun hmem => OddOrder.BG.Ch3.S10.sigma_conj g hmem⟩
    have h2 := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hmem
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  · exact ⟨fun hmem => absurd (Nat.prime_of_mem_primeFactors
        ((OddOrder.BG.Ch3.S10.mem_sigma_iff _ p).mp hmem).1) hp,
      fun hmem => absurd (Nat.prime_of_mem_primeFactors
        ((OddOrder.BG.Ch3.S10.mem_sigma_iff _ p).mp hmem).1) hp⟩

/-- `O_π` (`opiCoreInG`) commutes with conjugation (replicated from the private
`S07_Transitivity.conj_smul_opiCoreInG`). -/
private theorem conj_smul_opiCoreInG' [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]

/-- `M_σ` is conjugation-equivariant: `(Mᵍ)_σ = (M_σ)ᵍ`.  Used to move an element of `M*_σ` back to
its conjugate maximal subgroup when witnessing `ℓ_σ = 1`. -/
private theorem Msigma_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [conj_smul_opiCoreInG', sigma_conj_smul_eq]

/-- **BG Corollary 14.3** (mmd L3852): for `x ∈ M_σ^#` and a nonidentity `σ(M)'`-element `x'`
of `C_M(x)`, either (1) `π(⟨x'⟩) ⊆ κ(M)` and `C_G(x) ⊆ M`, or (2) `π(⟨x'⟩) ⊆ τ₂(M)`,
`ℓ_σ(x') = 1`, and `𝓜(C_G(x')) = {M}`.

Proof sketch (gated on §13 via Prop 14.2): a prime `p ∈ π(⟨x'⟩) ∩ τ₂(M)'` lies in
`τ₁(M) ∪ τ₃(M)`, and `C_{M_σ}(X) ⊇ ⟨x⟩ ≠ 1` for `X ∈ ℰ_p¹(⟨x'⟩)` forces `p ∈ κ(M)`; then
Lemma 14.1(b) gives `x' ∈ K`, `x ∈ C_{M_σ}(K)`, and Proposition 14.2(c) yields `C_G(x) ⊆ M`
(branch 1).  Otherwise `x'` is a `τ₂(M)`-element with `C_{M_σ}(x') ≠ 1`, so Corollary 12.10(e)
gives `𝓜(C_G(x')) = {M}` and Lemma 12.11(a) gives `ℓ_σ(x') = 1` (branch 2).

**Faithfulness (2026-06-15):** reformulated to the verbatim BG statement.  The earlier scaffold
had an `x ↔ x'` transposition (branch 1's body asserted the impossible `x' ∈ M_σ`), a missing
`x'`-centralizes-`x` hypothesis, and dropped `C_G(x) ⊆ M`, `ℓ_σ(x')`, and `𝓜(C_G(x'))`.
`ℓ_σ(x')` is carried by the `SigmaDecompositionData` `D` (`D.length x' = 1`).  Proof deferred
(gated on §13).  See `notes/bg/s14_typeP_counting.md`. -/
theorem sigma_diagnostic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hx : x ∈ sigmaSharp M) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cent : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'sigma : ∀ p ∈ piSet (Subgroup.closure {x'}),
      p ∉ OddOrder.BG.Ch3.S10.sigma M) :
    ((∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ kappa M) ∧
        Subgroup.centralizer ({x} : Set G) ≤ M) ∨
    ((∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M) ∧
        D.length x' = 1 ∧
        maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) = {M}) := by
  classical
  -- `x ∈ M_σ`, `x ≠ 1`.
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  have hclos : Subgroup.closure ({x'} : Set G) = Subgroup.zpowers x' :=
    (Subgroup.zpowers_eq_closure x').symm
  -- `x` centralizes `x'`.
  have hxCx' : x ∈ Subgroup.centralizer ({x'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact (Subgroup.mem_centralizer_iff.mp hx'cent x (Set.mem_singleton x)).symm
  -- `C_{M_σ}(x') ≠ 1` (it contains `x ≠ 1`).
  have hCx'ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x'} : Set G) ≠ ⊥ :=
    fun hbot => hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hxMσ, hxCx'⟩))
  by_cases hτ2 : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∈ tau2 M
  · -- **Branch 2**: `x'` is a `τ₂(M)`-element.
    refine Or.inr ⟨hτ2, ?_, maximalContaining_centralizer_eq_singleton_of_tau2_element hG hM
      hx'M hx'1 hτ2 hCx'ne⟩
    -- `ℓ_σ(x') = 1`: `x'` is a `σ(M*)`-element (Lemma 12.11(a)), hence `G`-conjugate into `M*_σ`
    -- (general Corollary 12.16(a)), so `𝓜_σ(x')` is nonempty.
    refine (D.length_one_iff x').mpr ⟨hx'1, ?_⟩
    -- `π(⟨x'⟩)` is nonempty (`x' ≠ 1`); pick a prime `q₀ ∈ π(⟨x'⟩) ⊆ τ₂(M)`.
    have hclosne : Subgroup.closure ({x'} : Set G) ≠ ⊥ := fun hbot =>
      hx'1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure (Set.mem_singleton x')))
    obtain ⟨q₀, hq₀mem⟩ : (piSet (Subgroup.closure ({x'} : Set G))).Nonempty :=
      Nat.nonempty_primeFactors.mpr (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')
        (Ne.symm fun h => hclosne (Subgroup.card_eq_one.mp h)))
    have hq₀prime : q₀.Prime := Nat.prime_of_mem_primeFactors hq₀mem
    haveI : Fact q₀.Prime := ⟨hq₀prime⟩
    have hq₀τ2 : q₀ ∈ tau2 M := hτ2 q₀ hq₀mem
    -- `E`-setup, a rank-2 `A ∈ ℰ_{q₀}²(E)` (push `ℰ_{q₀}²(M)` into `E₂`), and `M* ∈ ℳ(N_G(A))`.
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    obtain ⟨A₁, hA₁, hA₁M⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hq₀prime hq₀τ2
    obtain ⟨w, _, hwle⟩ := exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le hsetup.E₂_hall
      (tau2_subset_sigma_compl M) hA₁M (by
        intro r hr
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁M).toEquiv, hA₁.2,
          Nat.primeFactors_pow q₀ two_ne_zero, Nat.Prime.primeFactors hq₀prime] at hr
        rw [Finset.mem_singleton.mp hr]; exact hq₀τ2)
    have hA : MulAut.conj w • A₁ ∈ elemAbelianOfRank G q₀ 2 := conj_smul_mem_elemAbelianOfRank w hA₁
    have hAE : MulAut.conj w • A₁ ≤ E := hwle.trans hsetup.E₂_le
    have hAM : MulAut.conj w • A₁ ≤ M := hAE.trans hsetup.E_le
    have hAne : MulAut.conj w • A₁ ≠ ⊥ := by
      intro hbot
      have hc : Nat.card ↥(MulAut.conj w • A₁) = q₀ ^ 2 := hA.2
      rw [hbot, Subgroup.card_bot] at hc
      rcases Nat.pow_eq_one.mp hc.symm with h | h
      · exact hq₀prime.ne_one h
      · exact absurd h (by norm_num)
    obtain ⟨Mstar, hMstar_max, hMstar_ge⟩ :=
      OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
        hG hM hAne hAM
    have hMstarMem : Mstar ∈ maximalSubgroupsContaining
        (Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar_max, hMstar_ge⟩
    -- Lemma 12.11(a): every prime of `π(⟨x'⟩) ⊆ τ₂(M)` lies in `σ(M*)`.
    have hx'piMstar : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)
        (Subgroup.closure ({x'} : Set G)) := fun p hp =>
      (tau2_prime_mem_sigma_diff_beta hG hsetup hq₀τ2 hA hAE hMstarMem
        (Nat.prime_of_mem_primeFactors hp) (hτ2 p hp)).1
    -- general Corollary 12.16(a): `⟨x'⟩` is `G`-conjugate into `M*_σ`.
    have hzplt : Subgroup.closure ({x'} : Set G) < ⊤ :=
      lt_of_le_of_lt (by rw [hclos, Subgroup.zpowers_le]; exact hx'M)
        (mem_maximalSubgroups.mp hM).lt_top
    obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hMstar_max hclosne hzplt hx'piMstar
      (fun hN hnc => sigma_disjoint_of_nonconjugate hG hMstar_max hN hnc)
    -- `M' = (M*)^{g⁻¹}` is maximal and contains `x'` in its `σ`-core.
    refine ⟨MulAut.conj g⁻¹ • Mstar,
      mem_maximalSubgroups.mpr (isCoatom_conj_smul (mem_maximalSubgroups.mp hMstar_max)), ?_⟩
    rw [Msigma_conj_smul]
    have hconj : MulAut.conj g • x' ∈ OddOrder.BG.Ch3.S10.Msigma Mstar :=
      hg (Subgroup.smul_mem_pointwise_smul x' (MulAut.conj g) (Subgroup.closure ({x'} : Set G))
        (Subgroup.subset_closure (Set.mem_singleton x')))
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using hconj
  · -- **Branch 1**: some prime `p₀ ∈ π(⟨x'⟩)` lies in `τ₁(M) ∪ τ₃(M)`.
    left
    push Not at hτ2
    obtain ⟨p₀, hp₀mem, hp₀τ2⟩ := hτ2
    have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀mem
    haveI : Fact p₀.Prime := ⟨hp₀prime⟩
    have hp₀σ : p₀ ∉ OddOrder.BG.Ch3.S10.sigma M := hx'sigma p₀ hp₀mem
    -- `⟨x'⟩ ≤ M`, so `p₀ ∣ |M|`, and `p₀ ∤ |M_σ|`, hence `p₀ ∈ π(E)`.
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
    have hclosM : Subgroup.closure ({x'} : Set G) ≤ M := by
      rw [hclos, Subgroup.zpowers_le]; exact hx'M
    have hp₀cardclos : p₀ ∣ Nat.card ↥(Subgroup.closure ({x'} : Set G)) :=
      (Nat.mem_primeFactors.mp hp₀mem).2.1
    have hp₀M : p₀ ∣ Nat.card ↥M := hp₀cardclos.trans (Subgroup.card_dvd_of_le hclosM)
    have hp₀nMσ : ¬ p₀ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hdvd =>
      hp₀σ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p₀
        (Nat.mem_primeFactors.mpr ⟨hp₀prime, hdvd, Nat.card_pos.ne'⟩))
    have hp₀E : p₀ ∈ (Nat.card ↥E).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hp₀prime, ?_, Nat.card_pos.ne'⟩
      have hdvdME : p₀ ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥E := by
        rw [hsetup.card_Msigma_mul_card_E]; exact hp₀M
      exact (hp₀prime.dvd_mul.mp hdvdME).resolve_left hp₀nMσ
    have hp₀τ13 : p₀ ∈ tau1 M ∪ tau3 M := by
      rcases hsetup.mem_tau_union_of_mem_primeFactors hG hp₀E with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hp₀τ2
      · exact Or.inr h3
    -- `X₀ = ⟨w⟩` of order `p₀`, `≤ ⟨x'⟩`, with `x ∈ C_{M_σ}(X₀)`, so `p₀ ∈ κ(M)`.
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p₀
      (hclos ▸ hp₀cardclos : p₀ ∣ Nat.card ↥(Subgroup.zpowers x'))
    set X₀ : Subgroup G := Subgroup.zpowers (w : G) with hX₀def
    have hX₀le_clos : X₀ ≤ Subgroup.closure ({x'} : Set G) := by
      rw [hX₀def, hclos, Subgroup.zpowers_le]; exact w.2
    have hX₀M : X₀ ≤ M := hX₀le_clos.trans hclosM
    have hwcard : Nat.card ↥X₀ = p₀ := by
      rw [hX₀def, Nat.card_zpowers]
      exact (orderOf_injective (Subgroup.zpowers x').subtype
        (Subgroup.zpowers x').subtype_injective w).trans hw
    have hX₀elem : X₀ ∈ elemAbelianOfRank G p₀ 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hwcard, by rw [hwcard, pow_one]⟩
    have hX₀le_zp : X₀ ≤ Subgroup.zpowers x' := by
      rw [hX₀def, Subgroup.zpowers_le]; exact w.2
    -- `x` centralizes `X₀` (it centralizes `x'`, and `X₀ ≤ ⟨x'⟩`).
    have hcomm : Commute x x' :=
      Subgroup.mem_centralizer_iff.mp hx'cent x (Set.mem_singleton x)
    have hxCw : Commute x (w : G) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
      rw [← hn]; exact hcomm.zpow_right n
    have hxCX₀ : x ∈ Subgroup.centralizer (X₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hX₀def, SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hxCw.zpow_right m).symm
    have hCX₀ne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X₀ : Set G) ≠ ⊥ :=
      fun hbot => hx1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hxMσ, hxCX₀⟩))
    have hp₀κ : p₀ ∈ kappa M := ⟨hp₀prime, hp₀τ13, X₀, hX₀elem, hX₀M, hCX₀ne⟩
    -- A Hall `κ(M)`-subgroup `K ⊇ X₀`, a Hall `(κ∪σ)'`-subgroup `U`, and `Kstar = C_{M_σ}(K)`.
    have hX₀κ : ∀ q ∈ (Nat.card ↥X₀).primeFactors, q ∈ kappa M := by
      intro q hq
      rw [hwcard, hp₀prime.primeFactors, Finset.mem_singleton] at hq
      exact hq ▸ hp₀κ
    obtain ⟨K, hKM, hK, hX₀K⟩ := exists_isHallSubgroup_kappa_ge hG hM hX₀M hX₀κ
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
      ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
    have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
    have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
    have hP : IsTypeP M := ⟨p₀, hp₀κ⟩
    obtain ⟨_, _, hb1, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK
      (rfl : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) =
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) hU
    -- `C_M(x') ⊆ N_G(X₀) ⊓ M = K ⊔ K*` (Prop 14.2(b1)).
    have hb1X₀ := hb1 p₀ hp₀prime X₀ hX₀elem hX₀K
    have hCx'_le_CX₀ : Subgroup.centralizer ({x'} : Set G) ≤ Subgroup.centralizer (X₀ : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hX₀def, SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgw : Commute g (w : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
        rw [← hn]
        have hgx' : Commute x' g := Subgroup.mem_centralizer_iff.mp hg x' (Set.mem_singleton x')
        exact hgx'.symm.zpow_right n
      exact (hgw.zpow_right m).symm
    have hCMx'_le : Subgroup.centralizer ({x'} : Set G) ⊓ M ≤
        K ⊔ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hb1X₀]
      exact inf_le_inf_right _ (hCx'_le_CX₀.trans (Subgroup.centralizer_le_normalizer _))
    -- `x' ∈ K` (the `σ'`-part) and `x ∈ K*` (the `σ`-part) of `K ⊔ K* = K × K*`.
    set Kst : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      with hKstdef
    have hKstMσ : Kst ≤ OddOrder.BG.Ch3.S10.Msigma M := inf_le_left
    have hKstC : Kst ≤ Subgroup.centralizer (K : Set G) := inf_le_right
    -- `K` is normal in `K ⊔ K*` (`K*` centralizes `K`), so elements decompose as `k · s`.
    have hKnorm : K ⊔ Kst ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer (hKstC.trans (Subgroup.centralizer_le_normalizer _))
    haveI hKsNorm : ((K).subgroupOf (K ⊔ Kst)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
    have hsuptop : (K.subgroupOf (K ⊔ Kst)) ⊔ (Kst.subgroupOf (K ⊔ Kst)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    have hdecomp : ∀ z : G, z ∈ K ⊔ Kst → ∃ k ∈ K, ∃ s ∈ Kst, k * s = z := by
      intro z hz
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
        (hsuptop ▸ Subgroup.mem_top (⟨z, hz⟩ : ↥(K ⊔ Kst)))
      exact ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb,
        by have := congrArg Subtype.val hab; simpa using this⟩
    -- `K ∩ M_σ = ⊥` (`K` is a `κ(M) ⊆ σ(M)'`-group, `M_σ` a `σ(M)`-group).
    have hKMσbot : K ⊓ OddOrder.BG.Ch3.S10.Msigma M = ⊥ := by
      refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
      intro r hr hrK hrMσ
      have hrκ : r ∈ kappa M := hK.1 r (by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
        exact Nat.mem_primeFactors.mpr ⟨hr, hrK, Nat.card_pos.ne'⟩)
      exact kappa_subset_sigmaCompl hrκ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
    have hcardclos : Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' := by
      rw [hclos, Nat.card_zpowers]
    -- `x ∈ K*`: `x = k · s` with `k ∈ K`, `s ∈ K* ≤ M_σ`; `x ∈ M_σ` forces `k ∈ K ∩ M_σ = ⊥`.
    have hxsup : x ∈ K ⊔ Kst :=
      hCMx'_le (Subgroup.mem_inf.mpr ⟨hxCx', (OddOrder.BG.Ch3.S10.Msigma_le M) hxMσ⟩)
    have hxKstar : x ∈ Kst := by
      obtain ⟨k, hkK, s, hsKst, hks⟩ := hdecomp x hxsup
      have hkMσ : k ∈ OddOrder.BG.Ch3.S10.Msigma M := by
        have : k = x * s⁻¹ := by rw [← hks]; group
        rw [this]
        exact (OddOrder.BG.Ch3.S10.Msigma M).mul_mem hxMσ
          ((OddOrder.BG.Ch3.S10.Msigma M).inv_mem (hKstMσ hsKst))
      have hk1 : k = 1 := Subgroup.mem_bot.mp (hKMσbot ▸ Subgroup.mem_inf.mpr ⟨hkK, hkMσ⟩)
      rw [← hks, hk1, one_mul]; exact hsKst
    -- `x' ∈ K`: `x' = k · s` with `s ∈ K* ≤ M_σ`; `x'` is a `σ'`-element, so `s = 1`.
    have hx'sup : x' ∈ K ⊔ Kst :=
      hCMx'_le (Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_centralizer_iff.mpr (fun y hy => by rw [Set.mem_singleton_iff.mp hy]), hx'M⟩)
    have hx'K : x' ∈ K := by
      obtain ⟨k, hkK, s, hsKst, hks⟩ := hdecomp x' hx'sup
      have hcommks : Commute k s := Subgroup.mem_centralizer_iff.mp (hKstC hsKst) k hkK
      have hsM : s ∈ OddOrder.BG.Ch3.S10.Msigma M := hKstMσ hsKst
      -- `(k·s)^N = k^N · s^N = 1` (`N = orderOf x'`), so `k^N = (s^N)⁻¹ ∈ K ∩ M_σ = ⊥`.
      have hN : k ^ orderOf x' * s ^ orderOf x' = 1 := by
        rw [← hcommks.mul_pow, hks]; exact pow_orderOf_eq_one x'
      have hkN1 : k ^ orderOf x' = 1 := by
        have hmem : k ^ orderOf x' ∈ K ⊓ OddOrder.BG.Ch3.S10.Msigma M :=
          Subgroup.mem_inf.mpr ⟨K.pow_mem hkK _, by
            rw [eq_inv_of_mul_eq_one_left hN]
            exact (OddOrder.BG.Ch3.S10.Msigma M).inv_mem
              ((OddOrder.BG.Ch3.S10.Msigma M).pow_mem hsM _)⟩
        exact Subgroup.mem_bot.mp (hKMσbot ▸ hmem)
      have hsN1 : s ^ orderOf x' = 1 := by
        have := hN; rw [hkN1, one_mul] at this; exact this
      -- `orderOf s ∣ orderOf x'` and `orderOf s ∣ |M_σ|`, which are coprime, so `s = 1`.
      have hcop : Nat.Coprime (orderOf x') (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) :=
        coprime_of_forall_prime_not_dvd (fun r hr hrx' hrMσ => by
          exact hx'sigma r (by
            rw [piSet, Set.mem_setOf_eq, hcardclos]
            exact Nat.mem_primeFactors.mpr ⟨hr, hrx', (orderOf_pos_iff.mpr
              (isOfFinOrder_of_finite x')).ne'⟩)
            (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
              (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩)))
      have hsord : orderOf s = 1 := by
        have hdvd1 : orderOf s ∣ orderOf x' := orderOf_dvd_of_pow_eq_one hsN1
        have hdvd2 : orderOf s ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
          have h := orderOf_dvd_natCard (⟨s, hsM⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma M))
          rwa [← orderOf_injective (OddOrder.BG.Ch3.S10.Msigma M).subtype
            (OddOrder.BG.Ch3.S10.Msigma M).subtype_injective ⟨s, hsM⟩] at h
        have hg : orderOf s ∣ Nat.gcd (orderOf x')
            (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := Nat.dvd_gcd hdvd1 hdvd2
        rw [hcop] at hg
        exact Nat.dvd_one.mp hg
      have hs1 : s = 1 := orderOf_eq_one_iff.mp hsord
      rw [← hks, hs1, mul_one]; exact hkK
    refine ⟨?_, ?_⟩
    · -- `π(⟨x'⟩) ⊆ κ(M)`: `x' ∈ K`, `K` is a Hall `κ(M)`-subgroup.
      intro p hp
      rw [hclos] at hp
      have hpK : p ∈ (Nat.card ↥K).primeFactors := by
        refine Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, ?_, Nat.card_pos.ne'⟩
        exact ((Nat.mem_primeFactors.mp hp).2.1.trans
          (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx'K)))
      have hpKM : p ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact hK.1 p hpKM
    · -- `C_G(x) ⊆ M`: a rank-one `X₁ ≤ ⟨x⟩ ≤ K*` has `ℳ(C_G(X₁)) = {M}` (Prop 14.2(c)),
      -- and `C_G(x) ⊆ C_G(X₁) ⊆ M`.
      obtain ⟨p₁, hp₁, hp₁dvd⟩ := Nat.exists_prime_and_dvd
        (show orderOf x ≠ 1 from fun h => hx1 (orderOf_eq_one_iff.mp h))
      haveI : Fact p₁.Prime := ⟨hp₁⟩
      obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) p₁
        (by rw [Nat.card_zpowers]; exact hp₁dvd)
      have hvcard : Nat.card ↥(Subgroup.zpowers (v : G)) = p₁ := by
        rw [Nat.card_zpowers]
        exact (orderOf_injective (Subgroup.zpowers x).subtype
          (Subgroup.zpowers x).subtype_injective v).trans hv
      have hX₁elem : Subgroup.zpowers (v : G) ∈ elemAbelianOfRank G p₁ 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hvcard, by rw [hvcard, pow_one]⟩
      have hvx : (v : G) ∈ Subgroup.zpowers x := v.2
      have hX₁Kst : Subgroup.zpowers (v : G) ≤ Kst :=
        Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr hxKstar) hvx)
      have h𝓜 : maximalSubgroupsContaining
          (Subgroup.centralizer (↑(Subgroup.zpowers (v : G)) : Set G)) = {M} :=
        hc p₁ hp₁ (Subgroup.zpowers (v : G)) hX₁elem hX₁Kst
      have hCX₁M : Subgroup.centralizer (↑(Subgroup.zpowers (v : G)) : Set G) ≤ M :=
        (mem_maximalSubgroupsContaining.mp (by rw [h𝓜]; exact Set.mem_singleton M)).2
      refine le_trans ?_ hCX₁M
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hgx : Commute g x := (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
      have hgv : Commute g (v : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hvx
        rw [← hn]; exact hgx.zpow_right n
      exact ((hgv.zpow_right m).symm)

/-- Centralizer of `⟨x⟩` equals centralizer of `{x}` (replicated private helper). -/
private theorem centralizer_zpowers_eq_singleton' (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hc x (Subgroup.mem_zpowers x)
  · intro hc y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute x c from hc x rfl).zpow_left k).eq

/-- **Theorem 14.7 neighbour `κ`-transfer** (BG L3983-3991), step 1b of the §16-independent
pre-position: in the situation of `typeP_neighbor_embed`, every prime `q ∈ π(K*)` lies in
`κ(M_i)`.

Proof: take `X* = ⟨x'⟩ ∈ ℰ_q¹(K*)` (Cauchy).  Since `x ∈ X ⊆ M_{iσ}^#` centralizes `x'` (both
lie in `Z = K × K*` with `[K, K*] = 1`) and `x' ∈ K*` is a `σ(M_i)'`-element (Theorem 13.9 makes
`σ(M)` disjoint from `σ(M_i)`), Corollary 14.3 (`sigma_diagnostic`) applies to `(M_i, x, x')`.
Its branch 2 would give `ℳ(C_G(x')) = {M_i}`, contradicting Prop 14.2(c)'s `ℳ(C_G(x')) = {M}`
(`M ≠ M_i`); so branch 1 holds, giving `q ∈ π(⟨x'⟩) ⊆ κ(M_i)`.  (`sigma_diagnostic`'s `ℓ_σ`
carrier `D` is supplied by a dummy `SigmaDecompositionData`; only the branch dichotomy and its
`ℳ(C_G(x'))` clause are used, not `D.length`.) -/
theorem typeP_neighbor_kappa [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi := by
  classical
  obtain ⟨hnc, hZMi, hXMiσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hMi
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hMiMax : Mi ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hMi).1
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hMiMax hnc
  -- A dummy `ℓ_σ` carrier for `sigma_diagnostic`.
  let D : SigmaDecompositionData G :=
    { length := fun y => if y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty then 1 else 0
      length_one_iff := by
        intro y; by_cases h : y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty <;> simp [h] }
  -- An element `x ∈ X^#` lands in `M_{iσ}^#`.
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  haveI : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXne
  obtain ⟨xsub, hxsub⟩ := exists_ne (1 : ↥X)
  have hxX : (xsub : G) ∈ X := xsub.2
  have hxne : (xsub : G) ≠ 1 := fun h => hxsub (OneMemClass.coe_eq_one.mp h)
  have hxK : (xsub : G) ∈ K := hXK hxX
  have hxsharp : (xsub : G) ∈ sigmaSharp Mi := by
    rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    exact ⟨hXMiσ hxX, hxne⟩
  intro q hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  -- Cauchy: `x' ∈ K*` of order `q`.
  obtain ⟨x'sub, hx'ord⟩ := exists_prime_orderOf_dvd_card' q
    (Nat.dvd_of_mem_primeFactors hq : q ∣ Nat.card ↥Kstar)
  have hx'Kstar : (x'sub : G) ∈ Kstar := x'sub.2
  have hx'ord' : orderOf (x'sub : G) = q :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x'sub).trans hx'ord
  have hx'ne : (x'sub : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx'ord'
    exact (Nat.prime_of_mem_primeFactors hq).ne_one hx'ord'.symm
  have hX'card : Nat.card ↥(Subgroup.zpowers (x'sub : G)) = q := by rw [Nat.card_zpowers, hx'ord']
  have hX'mem : Subgroup.zpowers (x'sub : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hX'card, by rw [hX'card, pow_one]⟩
  have hX'Kstar : Subgroup.zpowers (x'sub : G) ≤ Kstar := Subgroup.zpowers_le.mpr hx'Kstar
  have hx'Mi : (x'sub : G) ∈ Mi := hZMi (Subgroup.mem_sup_right hx'Kstar)
  have hx'CK : (x'sub : G) ∈ Subgroup.centralizer (K : Set G) := by
    have h2 : (x'sub : G) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hKstar]; exact hx'Kstar
    exact (Subgroup.mem_inf.mp h2).2
  have hxCx' : (x'sub : G) ∈ Subgroup.centralizer ({(xsub : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_centralizer_iff.mp hx'CK (xsub : G) hxK
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr ⟨Fact.out,
      (Nat.dvd_of_mem_primeFactors hq).trans (Subgroup.card_dvd_of_le
        (by rw [hKstar]; exact inf_le_left : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M)),
      Nat.card_pos.ne'⟩)
  have hclos' : Subgroup.closure ({(x'sub : G)} : Set G) = Subgroup.zpowers (x'sub : G) :=
    (Subgroup.zpowers_eq_closure (x'sub : G)).symm
  have hcardclos : Nat.card ↥(Subgroup.closure ({(x'sub : G)} : Set G)) = q :=
    (congrArg (fun S : Subgroup G => Nat.card ↥S) hclos').trans hX'card
  have hx'sigma : ∀ r ∈ piSet (Subgroup.closure {(x'sub : G)}),
      r ∉ OddOrder.BG.Ch3.S10.sigma Mi := by
    intro r hr
    simp only [piSet, hcardclos, Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hq),
      Finset.mem_singleton] at hr
    rw [hr]; exact Set.disjoint_left.mp hσdisj hqσM
  rcases sigma_diagnostic hG D hMiMax hxsharp hx'Mi hx'ne hxCx' hx'sigma with
    ⟨hπκ, _⟩ | ⟨_, _, hℳ⟩
  · refine hπκ q ?_
    simp only [piSet, hcardclos, Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hq)]
    exact Finset.mem_singleton_self q
  · exfalso
    have hcX' := hc q (Nat.prime_of_mem_primeFactors hq) (Subgroup.zpowers (x'sub : G)) hX'mem
      hX'Kstar
    rw [centralizer_zpowers_eq_singleton'] at hcX'
    rw [hcX'] at hℳ
    exact hnc ((Set.singleton_eq_singleton_iff.mp hℳ) ▸ IsConjugateSubgroup.refl M)

/-! ## Theorem 14.4 and Lemma 14.5: sigma-length one centralizers -/

/-- **`N_{M_σ}(A) = 1` for a rank-2 `τ₂(M)`-subgroup `A ≤ E`** (the crux of Theorem 14.4(c)).
If `M ∈ 𝓜`, `p ∈ τ₂(M)`, and `A ∈ ℰ_p²(E)` for an `E`-setup of `M`, then
`N_G(A) ⊓ M_σ = 1`: Corollary 12.6(b) gives `M ⊓ N_G(A) = E`, and `M_σ ⊓ E = 1`
(`E` complements `M_σ`), so `N_G(A) ⊓ M_σ = (M ⊓ N_G(A)) ⊓ M_σ = E ⊓ M_σ = 1`. -/
theorem Msigma_inf_normalizer_eq_bot_of_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    Subgroup.normalizer (A : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = ⊥ := by
  have hNMA : M ⊓ Subgroup.normalizer (A : Set G) = E :=
    (centralizer_le_E_of_tau2 hG h hp hA hAE).2.1
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  calc Subgroup.normalizer (A : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M
      = Subgroup.normalizer (A : Set G) ⊓ (M ⊓ OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [inf_eq_right.mpr hMσM]
    _ = (M ⊓ Subgroup.normalizer (A : Set G)) ⊓ OddOrder.BG.Ch3.S10.Msigma M := by
        rw [← inf_assoc, inf_comm (Subgroup.normalizer (A : Set G)) M]
    _ = E ⊓ OddOrder.BG.Ch3.S10.Msigma M := by rw [hNMA]
    _ = ⊥ := by rw [inf_comm]; exact h.E_compl_inf

/-- **BG Theorem 14.4** (mmd L3869, D. Sibley for part (f)): if `x ∈ G^#` and `𝓜_σ(x)` is
nonempty (equivalently `ℓ_σ(x) = 1`), then `C_G(x)` has a normal Hall subgroup `R(x)` acting
sharply transitively on `𝓜_σ(x)`.  Furthermore, if `|𝓜_σ(x)| > 1` then `C_G(x)` lies in a
unique `N = N(x) ∈ 𝓜`, and for every `M ∈ 𝓜_σ(x)`:
(a) `R(x) = C_{N_σ}(x) ⊋ 1` (a normal Hall `σ(N)`-subgroup of `C_G(x)`),
(b) `C_G(x) = C_{M∩N}(x) R(x)`,
(c) `π(⟨x⟩) ⊆ τ₂(N) ⊆ σ(M)`,
(d) `π(M) ∩ σ(N) ⊆ β(N)`,
(e) `M ∩ N` complements `N_σ` in `N`, and
(f) `N ∈ 𝓜_F ∪ 𝓜_{P₂}`.

**Faithfulness (2026-06-15):** the earlier scaffold's over-claim is fixed — the `N`/type
structure is now **guarded by `|𝓜_σ(x)| > 1`** (in the single-maximal case `R(x) = 1` and
there is no `N(x)`, so BG asserts no such structure).  `R(x)` is pinned to its concrete value
`C_{N_σ}(x) = M_σ(N) ⊓ C_G(x)` (part (a)), `N` is unique (`∃!`), and parts (a),(c),(d),(e),(f)
are recorded.  **Deferred to §16:** the headline "`R(x)` normal in `C_G(x)` and **sharply
transitive** on `𝓜_σ(x)`" and part (b) are preserved verbatim in §16 (`RData` /
`ConjSharplyTransitiveOn`, Theorem D); this surface should cite §16 at proof time rather than
restating them (importing §16 here would be circular).  Proof gated on §13 (Thm 13.9 + the
Cor 14.3 funnel).  See `notes/bg/s14_typeP_counting.md`. -/
theorem sigmaLength_one_centralizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {x : G} (hx : x ≠ 1) (hlen : D.length x = 1) :
    (maximalSigmaSubgroupsOfElement x).Nonempty ∧
      (1 < (maximalSigmaSubgroupsOfElement x).ncard →
        ∃! N : Subgroup G, N ∈ maximalSubgroups G ∧
          Subgroup.centralizer ({x} : Set G) ≤ N ∧
          OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
          Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
            ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
              (Subgroup.centralizer ({x} : Set G))) ∧
          (∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 N) ∧
          (IsTypeF N ∨ IsTypeP2 N) ∧
          ∀ M ∈ maximalSigmaSubgroupsOfElement x,
            tau2 N ∩ piSet N ⊆ OddOrder.BG.Ch3.S10.sigma M ∧
            OddOrder.BG.Ch3.S10.sigma N ∩ piSet M ⊆ OddOrder.BG.Ch3.S10.beta N ∧
            Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
              ((M ⊓ N).subgroupOf N) ∧
            -- **(Sharp transitivity, BG Thm 14.4 headline)**: `R(x) = N_σ ∩ C_G(x)` acts
            -- *regularly* (sharply transitively) on `𝓜_σ(x)` by conjugation: for every other
            -- `L ∈ 𝓜_σ(x)` there is a *unique* `r ∈ R(x)` with `M^r = L`.
            (∀ L ∈ maximalSigmaSubgroupsOfElement x,
              ∃! r : G, (r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) ∧
                MulAut.conj r • M = L)) := by
  classical
  -- (Nonempty) `𝓜_σ(x)` is nonempty because `ℓ_σ(x) = 1`.
  obtain ⟨-, hne⟩ := (D.length_one_iff x).mp hlen
  refine ⟨hne, fun hgt => ?_⟩
  -- Setup (BG L3877): pick `M ∈ 𝓜_σ(x)`, a prime `q ∣ |x|`, and `g ∈ ⟨x⟩` of order `q`,
  -- giving `X = ⟨g⟩ ∈ ℰ_q¹(⟨x⟩)` with `X ≤ M_σ` and `q ∈ σ(M)`.
  obtain ⟨M, hMmax, hxMσ⟩ := hne
  have hord1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hqp, hqdvd⟩ := (orderOf x).exists_prime_and_dvd hord1
  haveI : Fact q.Prime := ⟨hqp⟩
  obtain ⟨gsub, hgord⟩ := exists_prime_orderOf_dvd_card' q
    (show q ∣ Nat.card ↥(Subgroup.zpowers x) by rw [Nat.card_zpowers]; exact hqdvd)
  have hgord' : orderOf (gsub : G) = q :=
    (orderOf_injective (Subgroup.zpowers x).subtype (Subgroup.zpowers x).subtype_injective
      gsub).trans hgord
  set X : Subgroup G := Subgroup.zpowers (gsub : G) with hXdef
  have hXcard : Nat.card ↥X = q := by rw [hXdef, Nat.card_zpowers, hgord']
  have hXelem : X ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXx : X ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr gsub.2
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    hXx.trans (Subgroup.zpowers_le.mpr hxMσ)
  have hqMσ : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hxMσ)
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqMσ, Nat.card_pos.ne'⟩)
  have hXq : IsPGroup q ↥X := IsPGroup.of_card (by rw [hXcard, pow_one])
  have hXMle : X ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  -- (Neighbour `N`) Since `|𝓜_σ(x)| ≥ 2`, pick `M' ∈ 𝓜_σ(x)` distinct from `M`.
  obtain ⟨M', hM'mem, hM'ne⟩ := Set.exists_ne_of_one_lt_ncard hgt M
  obtain ⟨hM'max, hxM'σ⟩ := hM'mem
  have hXM'σ : X ≤ OddOrder.BG.Ch3.S10.Msigma M' := hXx.trans (Subgroup.zpowers_le.mpr hxM'σ)
  have hXM'le : X ≤ M' := hXM'σ.trans (OddOrder.BG.Ch3.S10.Msigma_le M')
  have hqσM' : q ∈ OddOrder.BG.Ch3.S10.sigma M' :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M' q (Nat.mem_primeFactors.mpr
      ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M').orderOf_dvd_natCard hxM'σ),
        Nat.card_pos.ne'⟩)
  -- `M, M'` are conjugate (else Theorem 13.9 makes `σ(M), σ(M')` disjoint, but `q ∈ σ(M) ∩ σ(M')`).
  have hconj : ∃ g : G, MulAut.conj g • M = M' := by
    by_contra hnc
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hM'max hnc) hqσM hqσM'
  obtain ⟨g, hg⟩ := hconj
  -- Theorem 10.1(b): some `c ∈ C_G(X)` conjugates `M` to `M'`.
  have hX1 : X ≤ MulAut.conj (1 : G) • M := by rw [map_one, one_smul]; exact hXMle
  have hXg : X ≤ MulAut.conj g • M := by rw [hg]; exact hXM'le
  obtain ⟨c, hcC, hcconj⟩ :=
    (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hMmax hqσM hXne hXq).2.1 1 g hX1 hXg
  rw [map_one, one_smul] at hcconj
  have hcM' : MulAut.conj c • M = M' := by rw [hcconj]; exact hg
  -- Hence `C_G(X) ⊄ M`, so `N_G(X) ⊄ M`.
  have hNXM : ¬ Subgroup.normalizer (X : Set G) ≤ M := by
    intro hNXM
    have hcM : c ∈ M := hNXM (Subgroup.centralizer_le_normalizer (X : Set G) hcC)
    have hfix : MulAut.conj c • M = M :=
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hcM)
    have : M = M' := by rw [← hfix]; exact hcM'
    exact hM'ne this.symm
  -- Build the maximal `N ⊇ N_G(X)`; then `N ≠ M`.
  obtain ⟨N, hNmax, hNge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hMmax hXne hXMle
  have hNne : N ≠ M := fun he => hNXM (he ▸ hNge)
  -- `C_G(x) ≤ N`: `C_G(x) ≤ C_G(X) ≤ N_G(X) ≤ N` (as `X ≤ ⟨x⟩`).
  have hCxCX : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    rw [← centralizer_zpowers_eq_singleton' x]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXx)
  have hCxN : Subgroup.centralizer ({x} : Set G) ≤ N :=
    hCxCX.trans ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNge)
  -- (Prop 12.15) Build `S = Sylow_q(M ∩ N) ⊇ X` and apply Proposition 12.15 to `(M, q, X, N, S)`.
  have hNmem : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hNmax, hNge⟩
  have hXNle : X ≤ N := Subgroup.le_normalizer.trans hNge
  have hXMN : X ≤ M ⊓ N := le_inf hXMle hXNle
  have hXsub_pg : IsPGroup q ↥(X.subgroupOf (M ⊓ N)) :=
    hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXMN).symm
  obtain ⟨Psub, hPsub⟩ := hXsub_pg.exists_le_sylow
  set S : Subgroup G := (Psub : Subgroup ↥(M ⊓ N)).map (M ⊓ N).subtype with hSdef
  have hSle : S ≤ M ⊓ N := Subgroup.map_subtype_le _
  have hSq : IsPGroup q ↥S :=
    Psub.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M ⊓ N).subtype_injective)
  have hXS : X ≤ S := by
    rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hXMN]; exact Subgroup.map_mono hPsub
  have hPsubeq : S.subgroupOf (M ⊓ N) = Psub := by
    rw [hSdef]; exact Subgroup.comap_map_eq_self_of_injective (M ⊓ N).subtype_injective _
  have hSmax : ∀ T : Subgroup G, T ≤ M ⊓ N → IsPGroup q ↥T → S ≤ T → S = T := by
    intro T hTle hTq hST
    have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M ⊓ N)) :=
      hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
    have hTeq := Psub.3 hTsub_pg (by rw [← hPsubeq]; exact Subgroup.comap_mono hST)
    rw [hSdef, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
  have h1215 := sigma_subgroup_maximal_interaction hG hMmax hqσM hXMle hXne hXq hNmem hNne
    hSle hXS hSq hSmax
  -- (a) `M, N` nonconjugate ⟹ (Theorem 13.9) `σ(M) ∩ σ(N) = ∅` ⟹ `q ∉ σ(N)`.
  have hqnσN : q ∉ OddOrder.BG.Ch3.S10.sigma N := fun hqσN =>
    Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hNmax h1215.1) hqσM hqσN
  -- Proposition 12.15(e): `q ∈ τ₂(N)`, `(d)`, and `(e)` (`M ∩ N` complements `N_σ` in `N`).
  obtain ⟨hqτ2N, hdN, hsigmaInf, hsigmaSup⟩ := h1215.2.2.2.2 hqnσN
  -- `x ∈ N` (as `x ∈ C_G(x) ≤ N`).
  have hxN : x ∈ N := hCxN (Subgroup.mem_centralizer_iff.mpr
    (fun h hh => by rw [Set.mem_singleton_iff.mp hh]))
  -- `R(x) = N_σ ∩ C_G(x) ≠ 1` (BG's `u`-construction: a nontrivial `σ(N)`-element of `C_G(x)`).
  have hxMmem : x ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  have hRx : OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    -- `N_G(M) = M` (maximal ⟹ self-normalizing).
    have hMne : M ≠ ⊥ := fun hb => hXne (le_bot_iff.mp (hb ▸ hXMle))
    have hNMle : Subgroup.normalizer M ≤ M := by
      rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
      · exact heq.ge
      · rcases hG.simple.eq_bot_or_eq_top_of_normal M
            (Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hMmax).2 _ hlt)) with hb | ht
        · exact absurd hb hMne
        · exact absurd ht (mem_maximalSubgroups.mp hMmax).1
    -- Decompose `c = v * a` with `v ∈ N_σ`, `a ∈ M ⊓ N` (in `↥N`, since `N_σ ⊴ N`).
    have hcN : c ∈ N := ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNge) hcC
    have hMσN_le : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
    haveI hH'normal : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hsup' : (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N ⊔ (M ⊓ N).subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hMσN_le inf_le_right, hsigmaSup, Subgroup.subgroupOf_self]
    have hc'mem : (⟨c, hcN⟩ : ↥N) ∈
        (↑((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) *
          ↑((M ⊓ N).subgroupOf N) : Set ↥N) := by
      rw [← Subgroup.normal_mul, hsup']; exact Subgroup.mem_top _
    obtain ⟨vsub, hvsub, asub, hasub, hva⟩ := hc'mem
    have hvMσ : (vsub : G) ∈ OddOrder.BG.Ch3.S10.Msigma N := Subgroup.mem_subgroupOf.mp hvsub
    have haM : (asub : G) ∈ M := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hasub)).1
    have hcva : (vsub : G) * (asub : G) = c := by
      have := congrArg (Subgroup.subtype N) hva; simpa using this
    -- `conj v • M = M'` (as `a ∈ M`), so `v ≠ 1`.
    have hvM' : MulAut.conj (vsub : G) • M = M' := by
      have ha_fix : MulAut.conj (asub : G) • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer haM)
      rw [← hcM', ← hcva, map_mul, mul_smul, ha_fix]
    have hvne : (vsub : G) ≠ 1 := by
      intro hv1; rw [hv1, map_one, one_smul] at hvM'; exact hM'ne hvM'.symm
    -- `x⁻¹ v x ∈ N_σ` (normal, `x ∈ N`).
    have hconjMσ : x⁻¹ * (vsub : G) * x ∈ OddOrder.BG.Ch3.S10.Msigma N := by
      have h := hH'normal.conj_mem vsub hvsub (⟨x, hxN⟩⁻¹)
      have := Subgroup.mem_subgroupOf.mp h; simpa using this
    -- `conj (x⁻¹ v x) • M = conj v • M` (key step: `M^x = M`, `M'^{x⁻¹} = M'`).
    have hxM'mem : x ∈ M' := OddOrder.BG.Ch3.S10.Msigma_le M' hxM'σ
    have hkey : MulAut.conj (x⁻¹ * (vsub : G) * x) • M = MulAut.conj (vsub : G) • M := by
      have hxM : MulAut.conj x • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxMmem)
      have hxM' : MulAut.conj x⁻¹ • M' = M' :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (M'.inv_mem hxM'mem))
      calc MulAut.conj (x⁻¹ * (vsub : G) * x) • M
          = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • (MulAut.conj x • M)) := by
            rw [map_mul, map_mul, mul_smul, mul_smul]
        _ = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • M) := by rw [hxM]
        _ = MulAut.conj x⁻¹ • M' := by rw [hvM']
        _ = M' := hxM'
        _ = MulAut.conj (vsub : G) • M := hvM'.symm
    -- `v⁻¹ (x⁻¹ v x) ∈ N_G(M) ∩ N_σ = M ∩ N_σ = ⊥`, hence `x⁻¹ v x = v`, i.e. `v ∈ C_G(x)`.
    have hmemNM : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ Subgroup.normalizer M := by
      apply mem_normalizer_of_conj_smul_eq_self
      rw [map_mul, mul_smul, hkey, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hmemMσ : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ OddOrder.BG.Ch3.S10.Msigma N :=
      (OddOrder.BG.Ch3.S10.Msigma N).mul_mem
        ((OddOrder.BG.Ch3.S10.Msigma N).inv_mem hvMσ) hconjMσ
    have hmem1 : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) = 1 := by
      have hinbot : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ (⊥ : Subgroup G) := by
        rw [← hsigmaInf]
        exact Subgroup.mem_inf.mpr ⟨hmemMσ,
          Subgroup.mem_inf.mpr ⟨hNMle hmemNM, hMσN_le hmemMσ⟩⟩
      exact Subgroup.mem_bot.mp hinbot
    have hvx : x⁻¹ * (vsub : G) * x = (vsub : G) := (inv_mul_eq_one.mp hmem1).symm
    have hvCx : (vsub : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      have hcomm : x * (vsub : G) = (vsub : G) * x := by nth_rewrite 1 [← hvx]; group
      exact hcomm
    intro hbot
    exact hvne (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hvMσ, hvCx⟩))
  -- `π(⟨x⟩) ⊆ τ₂(N)` (Corollary 14.3, since `x` is not a `κ(N)`-element).
  have hcardx : Nat.card ↥(Subgroup.closure ({x} : Set G)) = orderOf x := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hπτ2 : ∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 N := by
    -- A nonidentity `w ∈ N_σ` centralizing `x` (from `R(x) ≠ 1`).
    haveI : Nontrivial ↥(OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hRx
    obtain ⟨wsub, hwsub⟩ :=
      exists_ne (1 : ↥(OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)))
    have hwmem := wsub.2
    have hwne : (wsub : G) ≠ 1 := fun h => hwsub (OneMemClass.coe_eq_one.mp h)
    obtain ⟨hwMσ, hwCx⟩ := Subgroup.mem_inf.mp hwmem
    have hwsharp : (wsub : G) ∈ sigmaSharp N := by
      rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
      exact ⟨hwMσ, hwne⟩
    have hxCw : x ∈ Subgroup.centralizer ({(wsub : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hwCx x (Set.mem_singleton x)).symm
    -- `π(⟨x⟩) ⊆ σ(M) ⊆ σ(N)'` (since `x ∈ M_σ` and `σ(M) ∩ σ(N) = ∅` by Theorem 13.9).
    have hxσN : ∀ p ∈ piSet (Subgroup.closure {x}), p ∉ OddOrder.BG.Ch3.S10.sigma N := by
      intro p hp
      have hp' : p ∈ (orderOf x).primeFactors := by
        rw [piSet, Set.mem_setOf_eq, hcardx] at hp; exact hp
      have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hp', (Nat.dvd_of_mem_primeFactors hp').trans
            ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hxMσ), Nat.card_pos.ne'⟩)
      exact Set.disjoint_left.mp
        (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hNmax h1215.1) hpσM
    -- Corollary 14.3: branch κ is impossible (`q ∈ τ₂(N)` has `r_q = 2 ≠ 1`), so the τ₂ branch holds.
    rcases sigma_diagnostic hG D hNmax hwsharp hxN hx hxCw hxσN with ⟨hκ, _⟩ | ⟨hτ2, _, _⟩
    · exfalso
      have hqπ : q ∈ piSet (Subgroup.closure ({x} : Set G)) := by
        rw [piSet, Set.mem_setOf_eq, hcardx]
        exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩
      have h2 := ((mem_tau2_iff N q).mp hqτ2N).2
      rcases (hκ q hqπ).2.1 with h1 | h3
      · exact absurd (((mem_tau1_iff N q).mp h1).2.2.symm.trans h2) (by norm_num)
      · exact absurd (((mem_tau3_iff N q).mp h3).2.2.symm.trans h2) (by norm_num)
    · exact hτ2
  -- `ℳ(C_G(x)) = {N}` (Corollary 14.3 uniqueness clause).
  have hsingleton : maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} :=
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx hπτ2 hRx
  refine ⟨N, ⟨hNmax, hCxN, hRx, ?_, hπτ2, ?_, ?_⟩, ?_⟩
  · -- `R(x) = N_σ ∩ C_G(x)` is a Hall `σ(N)`-subgroup of `C_G(x)`: it is a `σ(N)`-group, and its
    -- index `(N_σ).relIndex C_G(x) ∣ (N_σ).relIndex N = [N : N_σ] ∣ [G : N_σ]` is `σ(N)'`.
    haveI hK₀normal : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≤
          Subgroup.centralizer ({x} : Set G))).toEquiv] at hp
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1.trans
          (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    · intro p hp hpσ
      rw [Subgroup.inf_subgroupOf_right] at hp
      have hdvd1 : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf
          (Subgroup.centralizer ({x} : Set G))).index ∣
          ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index := by
        have h := Subgroup.relIndex_dvd_index_of_normal
          (H := (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          (K := (Subgroup.centralizer ({x} : Set G)).subgroupOf N)
        rwa [Subgroup.relIndex_subgroupOf hCxN] at h
      have hdvd2 : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index ∣
          (OddOrder.BG.Ch3.S10.Msigma N).index :=
        Subgroup.relIndex_dvd_index_of_le (OddOrder.BG.Ch3.S10.Msigma_le N)
      exact (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax).2 p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1,
          ((Nat.mem_primeFactors.mp hp).2.1.trans hdvd1).trans hdvd2,
          Subgroup.index_ne_zero_of_finite⟩) hpσ
  · -- `(f)`: `N ∈ 𝓜_F ∪ 𝓜_{P₂}`.  Either `κ(N) = ∅` (type F), or `κ(N) ≠ ∅` and, since
    -- `q ∈ τ₂(N) ⊆ π(N) - σ(N)` but `q ∉ κ(N)` (as `κ(N) ⊆ τ₁(N) ∪ τ₃(N)` has `r_q = 1 ≠ 2`),
    -- `κ(N) ≠ π(N) - σ(N)`, so `N ∉ 𝓜_{P₁}` (type P₂).
    by_cases hk : kappa N = ∅
    · exact Or.inl hk
    · refine Or.inr ⟨Set.nonempty_iff_ne_empty.mpr hk, fun heq => ?_⟩
      have hq_notin : q ∉ kappa N := by
        intro hqk
        have h2 := ((mem_tau2_iff N q).mp hqτ2N).2
        rcases hqk.2.1 with h1 | h3
        · exact absurd (((mem_tau1_iff N q).mp h1).2.2.symm.trans h2) (by norm_num)
        · exact absurd (((mem_tau3_iff N q).mp h3).2.2.symm.trans h2) (by norm_num)
      have hq_in : q ∈ sigmaComplementPrimes N :=
        ⟨Nat.mem_primeFactors.mpr ⟨hqp, hXcard ▸ Subgroup.card_dvd_of_le hXNle, Nat.card_pos.ne'⟩,
          hqnσN⟩
      rw [heq] at hq_notin
      exact hq_notin hq_in
  · -- per-`M` part `(c)`, `(d)`, `(e)`.  Fix `M₂ ∈ 𝓜_σ(x)` and re-run Proposition 12.15 for
    -- `(M₂, q, X, N)`: `N ≠ M₂` (as `x ∈ M₂_σ` but `x ∉ N_σ`), and `q ∉ σ(N)` (`q ∈ π(⟨x⟩) ⊆ τ₂(N)`).
    intro M₂ hM₂mem
    obtain ⟨hM₂max, hxM₂σ⟩ := hM₂mem
    haveI hMσNnormal : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hMσN_le : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
    have hXM₂σ : X ≤ OddOrder.BG.Ch3.S10.Msigma M₂ := hXx.trans (Subgroup.zpowers_le.mpr hxM₂σ)
    have hXM₂le : X ≤ M₂ := hXM₂σ.trans (OddOrder.BG.Ch3.S10.Msigma_le M₂)
    have hqσM₂ : q ∈ OddOrder.BG.Ch3.S10.sigma M₂ :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ q (Nat.mem_primeFactors.mpr
        ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M₂).orderOf_dvd_natCard hxM₂σ),
          Nat.card_pos.ne'⟩)
    have hqπ : q ∈ piSet (Subgroup.closure ({x} : Set G)) := by
      rw [piSet, Set.mem_setOf_eq, hcardx]
      exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩
    have hqnσN : q ∉ OddOrder.BG.Ch3.S10.sigma N := fun h => tau2_subset_sigma_compl N (hπτ2 q hqπ) h
    have hNM₂ : N ≠ M₂ := fun heq => hqnσN (heq ▸ hqσM₂)
    -- Build `S₂ = Sylow_q(M₂ ∩ N) ⊇ X`.
    have hXM₂N : X ≤ M₂ ⊓ N := le_inf hXM₂le hXNle
    have hXsub_pg₂ : IsPGroup q ↥(X.subgroupOf (M₂ ⊓ N)) :=
      hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXM₂N).symm
    obtain ⟨Psub₂, hPsub₂⟩ := hXsub_pg₂.exists_le_sylow
    set S₂ : Subgroup G := (Psub₂ : Subgroup ↥(M₂ ⊓ N)).map (M₂ ⊓ N).subtype with hS₂def
    have hS₂le : S₂ ≤ M₂ ⊓ N := Subgroup.map_subtype_le _
    have hS₂q : IsPGroup q ↥S₂ :=
      Psub₂.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M₂ ⊓ N).subtype_injective)
    have hXS₂ : X ≤ S₂ := by
      rw [hS₂def, ← Subgroup.map_subgroupOf_eq_of_le hXM₂N]; exact Subgroup.map_mono hPsub₂
    have hPsub₂eq : S₂.subgroupOf (M₂ ⊓ N) = Psub₂ := by
      rw [hS₂def]; exact Subgroup.comap_map_eq_self_of_injective (M₂ ⊓ N).subtype_injective _
    have hSmax₂ : ∀ T : Subgroup G, T ≤ M₂ ⊓ N → IsPGroup q ↥T → S₂ ≤ T → S₂ = T := by
      intro T hTle hTq hST
      have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M₂ ⊓ N)) :=
        hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
      have hTeq := Psub₂.3 hTsub_pg (by rw [← hPsub₂eq]; exact Subgroup.comap_mono hST)
      rw [hS₂def, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
    have h1215₂ := sigma_subgroup_maximal_interaction hG hM₂max hqσM₂ hXM₂le hXne hXq hNmem hNM₂
      hS₂le hXS₂ hS₂q hSmax₂
    obtain ⟨_, hdN₂, hsigmaInf₂, hsigmaSup₂⟩ := h1215₂.2.2.2.2 hqnσN
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (c) `τ₂(N) ⊆ σ(M₂)` (Corollary 12.6 argument).  Take `A ∈ ℰ_p²(N)` inside the complement
      -- `M₂ ∩ N` (= an `E`-setup `E_N` of `N` by `exists_subgroupESetup_with_le`); then `A ⊴ E_N`
      -- (Cor 12.6(a)) and `x ∈ M₂∩N = E_N` normalises `A`, so `x ∈ N_{M₂σ}(A) ⊋ 1`.  As `A ≤ M₂`
      -- has rank 2, `p ∈ σ(M₂) ∪ τ₂(M₂)`; if `p ∈ τ₂(M₂)` the crux helper forces `N_{M₂σ}(A) = 1`.
      intro p hp
      obtain ⟨hpτ2N, hppiN⟩ := hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppiN
      haveI : Fact p.Prime := ⟨hpp⟩
      have hM₂N_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma N)ᶜ) (M₂ ⊓ N) := by
        intro r hr
        rw [Set.mem_compl_iff]
        intro hrσN
        haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r
          (Nat.dvd_of_mem_primeFactors hr : r ∣ Nat.card ↥(M₂ ⊓ N))
        have hzord : orderOf (z : G) = r :=
          (orderOf_injective (M₂ ⊓ N).subtype (M₂ ⊓ N).subtype_injective z).trans hz
        have hzne : (z : G) ≠ 1 := by
          intro h; rw [h, orderOf_one] at hzord
          exact (Nat.prime_of_mem_primeFactors hr).ne_one hzord.symm
        have hzp_le : Subgroup.zpowers (z : G) ≤ M₂ ⊓ N := Subgroup.zpowers_le.mpr z.2
        have hzp_pi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N)
            (Subgroup.zpowers (z : G)) := by
          intro s hs
          rw [Nat.card_zpowers, hzord,
            Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hr), Finset.mem_singleton] at hs
          rw [hs]; exact hrσN
        have hzp_Msigma : Subgroup.zpowers (z : G) ≤ OddOrder.BG.Ch3.S10.Msigma N :=
          OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
            (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax) (hzp_le.trans inf_le_right) hzp_pi
        have hzp_bot : Subgroup.zpowers (z : G) ≤ ⊥ := by
          rw [← hsigmaInf₂]; exact le_inf hzp_Msigma hzp_le
        exact hzne (Subgroup.mem_bot.mp (hzp_bot (Subgroup.mem_zpowers (z : G))))
      obtain ⟨EN, E₁N, E₂N, E₃N, hN_E, hM₂N_le_EN, _⟩ :=
        exists_subgroupESetup_with_le hG hNmax inf_le_right hM₂N_pi
      have hEN_eq : EN = M₂ ⊓ N := by
        have hcompl_EN : Subgroup.IsComplement'
            ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) (EN.subgroupOf N) := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          · rw [disjoint_iff, eq_bot_iff]
            rintro a ha; rw [Subgroup.mem_inf] at ha
            have hav : (a : G) ∈ (⊥ : Subgroup G) := by
              rw [← hN_E.E_compl_inf]
              exact Subgroup.mem_inf.mpr
                ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
            rw [Subgroup.mem_bot] at hav; rw [Subgroup.mem_bot]; exact OneMemClass.coe_eq_one.mp hav
          · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hMσN_le hN_E.E_le,
              hN_E.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]
        have hcompl_M₂N : Subgroup.IsComplement'
            ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ((M₂ ⊓ N).subgroupOf N) := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          · rw [disjoint_iff, eq_bot_iff]
            rintro a ha; rw [Subgroup.mem_inf] at ha
            have hav : (a : G) ∈ (⊥ : Subgroup G) := by
              rw [← hsigmaInf₂]
              exact Subgroup.mem_inf.mpr
                ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
            rw [Subgroup.mem_bot] at hav; rw [Subgroup.mem_bot]; exact OneMemClass.coe_eq_one.mp hav
          · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hMσN_le inf_le_right,
              hsigmaSup₂, Subgroup.subgroupOf_self, Subgroup.coe_top]
        have hcardEq : Nat.card ↥(EN.subgroupOf N) = Nat.card ↥((M₂ ⊓ N).subgroupOf N) :=
          Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcompl_EN.card_mul.trans hcompl_M₂N.card_mul.symm)
        have hcard : Nat.card ↥EN = Nat.card ↥(M₂ ⊓ N) := by
          rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_E.E_le).toEquiv,
            ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M₂ ⊓ N ≤ N)).toEquiv]
          exact hcardEq
        exact (Subgroup.eq_of_le_of_card_ge hM₂N_le_EN (le_of_eq hcard)).symm
      obtain ⟨A₁, hA₁, hA₁N⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hpp hpτ2N
      obtain ⟨w, _, hwle⟩ := exists_conj_smul_le_hallPiece hG hN_E hN_E.E₂_le hN_E.E₂_hall
        (tau2_subset_sigma_compl N) hA₁N (by
          intro r hr
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁N).toEquiv, hA₁.2,
            Nat.primeFactors_pow p two_ne_zero, Nat.Prime.primeFactors hpp] at hr
          rw [Finset.mem_singleton.mp hr]; exact hpτ2N)
      have hA : MulAut.conj w • A₁ ∈ elemAbelianOfRank G p 2 := conj_smul_mem_elemAbelianOfRank w hA₁
      have hAEN : MulAut.conj w • A₁ ≤ EN := hwle.trans hN_E.E₂_le
      have hAM₂ : MulAut.conj w • A₁ ≤ M₂ := by rw [hEN_eq] at hAEN; exact hAEN.trans inf_le_left
      -- `A ⊴ E_N` (Cor 12.6(a)); `x ∈ M₂∩N = E_N` ⟹ `x` normalises `A`; `x ∈ M₂_σ`.
      have hAnormalEN : EN ≤ Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G) :=
        (elemAb_normal_in_E_of_tau2 hG hN_E hpτ2N hA hAEN).1.1
      have hxEN : x ∈ EN := by
        rw [hEN_eq]; exact Subgroup.mem_inf.mpr ⟨OddOrder.BG.Ch3.S10.Msigma_le M₂ hxM₂σ, hxN⟩
      have hx_in : x ∈ Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G) ⊓
          OddOrder.BG.Ch3.S10.Msigma M₂ :=
        Subgroup.mem_inf.mpr ⟨hAnormalEN hxEN, hxM₂σ⟩
      -- If `p ∉ σ(M₂)` then `p ∈ τ₂(M₂)` (rank 2), so Cor 12.6(b) kills `N_{M₂σ}(A)` — contradiction.
      by_contra hpσM₂
      have hAM₂_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M₂)ᶜ)
          (MulAut.conj w • A₁) := by
        intro r hr
        rw [hA.2, Nat.primeFactors_pow p two_ne_zero, Nat.Prime.primeFactors hpp,
          Finset.mem_singleton] at hr
        rw [hr]; exact hpσM₂
      obtain ⟨EM₂, _, _, _, hM₂_E, hAEM₂, _⟩ :=
        exists_subgroupESetup_with_le hG hM₂max hAM₂ hAM₂_pi
      have hpτ2M₂ : p ∈ tau2 M₂ := by
        rw [mem_tau2_iff]
        have hpcardEM₂ : p ∈ (Nat.card ↥EM₂).primeFactors := by
          refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
          have hpA : p ∣ Nat.card ↥(MulAut.conj w • A₁) := by
            rw [hA.2]; exact dvd_pow_self p two_ne_zero
          exact hpA.trans (Subgroup.card_dvd_of_le hAEM₂)
        refine ⟨hpσM₂, le_antisymm (hM₂_E.pRank_M_le_two hG hpcardEM₂) ?_⟩
        have hAea' : ((MulAut.conj w • A₁).subgroupOf M₂).IsElementaryAbelian p :=
          IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM₂).symm
            (mem_elemAbelianOfRank.mp hA).1
        have h := le_pRank ((MulAut.conj w • A₁).subgroupOf M₂) hAea'
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM₂).toEquiv, hA.2,
          Nat.log_pow hpp.one_lt] at h
      have hbot := Msigma_inf_normalizer_eq_bot_of_tau2 hG hM₂_E hpτ2M₂ hA hAEM₂
      rw [hbot, Subgroup.mem_bot] at hx_in
      exact hx hx_in
    · -- (d) `σ(N) ∩ π(M₂) ⊆ β(N)`.
      intro r hr; exact hdN₂ r hr.2 hr.1
    · -- (e) `M₂ ∩ N` complements `N_σ` in `N` (Proposition 12.15(e)'s `⊓ = ⊥`, `⊔ = N`).
      have hinf₂' : Disjoint ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          ((M₂ ⊓ N).subgroupOf N) := by
        rw [disjoint_iff, eq_bot_iff]
        rintro a ha
        rw [Subgroup.mem_inf] at ha
        have hav : (a : G) ∈ (⊥ : Subgroup G) := by
          rw [← hsigmaInf₂]
          exact Subgroup.mem_inf.mpr
            ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
        rw [Subgroup.mem_bot] at hav
        rw [Subgroup.mem_bot]; exact OneMemClass.coe_eq_one.mp hav
      have hsup₂' : (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N ⊔ (M₂ ⊓ N).subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hMσN_le inf_le_right, hsigmaSup₂, Subgroup.subgroupOf_self]
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hinf₂'
      rw [← Subgroup.normal_mul, hsup₂', Subgroup.coe_top]
    · -- **(Sharp transitivity)**: `R(x) = N_σ ∩ C_G(x)` acts regularly on `𝓜_σ(x)`
      -- (BG L3896-3900). For `L ∈ 𝓜_σ(x)`: `L = M₂^c` for some `c ∈ C_G(X)` (Theorem 10.1(b)
      -- fusion); write `c = v·a`, `v ∈ N_σ`, `a ∈ M₂∩N` (complement `N = N_σ(M₂∩N)`), so
      -- `conj v • M₂ = L`. Then `conj (x⁻¹vx) • M₂ = conj v • M₂` + freeness (`N_G(M₂)∩N_σ = 1`)
      -- forces `x⁻¹vx = v`, i.e. `v ∈ C_G(x)`; uniqueness is the same freeness argument.
      intro L hLmem
      obtain ⟨hLmax, hxLσ⟩ := hLmem
      have hxM₂mem : x ∈ M₂ := OddOrder.BG.Ch3.S10.Msigma_le M₂ hxM₂σ
      have hxLmem : x ∈ L := OddOrder.BG.Ch3.S10.Msigma_le L hxLσ
      -- `N_G(M₂) = M₂` (maximal ⟹ self-normalizing).
      have hM₂ne : M₂ ≠ ⊥ := fun hb => hXne (le_bot_iff.mp (hb ▸ hXM₂le))
      have hN_M₂_le : Subgroup.normalizer M₂ ≤ M₂ := by
        rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M₂)) with heq | hlt
        · exact heq.ge
        · rcases hG.simple.eq_bot_or_eq_top_of_normal M₂
              (Subgroup.normalizer_eq_top_iff.mp
                ((mem_maximalSubgroups.mp hM₂max).2 _ hlt)) with hb | ht
          · exact absurd hb hM₂ne
          · exact absurd ht (mem_maximalSubgroups.mp hM₂max).1
      -- `L` conjugate to `M₂` (else Thm 13.9 σ-disjoint, but `q ∈ σ(M₂) ∩ σ(L)`).
      have hqσL : q ∈ OddOrder.BG.Ch3.S10.sigma L :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup L q (Nat.mem_primeFactors.mpr
          ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma L).orderOf_dvd_natCard hxLσ),
            Nat.card_pos.ne'⟩)
      obtain ⟨gL, hgL⟩ : ∃ g : G, MulAut.conj g • M₂ = L := by
        by_contra hnc
        exact Set.disjoint_left.mp
          (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM₂max hLmax hnc) hqσM₂ hqσL
      -- Fusion (Theorem 10.1(b)): `c ∈ C_G(X)` with `conj c • M₂ = L`.
      have hXLle : X ≤ L :=
        (hXx.trans (Subgroup.zpowers_le.mpr hxLσ)).trans (OddOrder.BG.Ch3.S10.Msigma_le L)
      have hXM₂' : X ≤ MulAut.conj (1 : G) • M₂ := by rw [map_one, one_smul]; exact hXM₂le
      have hXgL : X ≤ MulAut.conj gL • M₂ := by rw [hgL]; exact hXLle
      obtain ⟨c, hcC, hcconj⟩ :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM₂max hqσM₂ hXne hXq).2.1 1 gL
          hXM₂' hXgL
      rw [map_one, one_smul] at hcconj
      have hcL : MulAut.conj c • M₂ = L := by rw [hcconj, hgL]
      -- `c ∈ N`; decompose `c = v · a` with `v ∈ N_σ`, `a ∈ M₂ ⊓ N`.
      have hcN : c ∈ N := ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNge) hcC
      have hsup₂'' :
          (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N ⊔ (M₂ ⊓ N).subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hMσN_le inf_le_right, hsigmaSup₂,
          Subgroup.subgroupOf_self]
      have hc'mem : (⟨c, hcN⟩ : ↥N) ∈
          (↑((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) *
            ↑((M₂ ⊓ N).subgroupOf N) : Set ↥N) := by
        rw [← Subgroup.normal_mul, hsup₂'']; exact Subgroup.mem_top _
      obtain ⟨vsub, hvsub, asub, hasub, hva⟩ := hc'mem
      have hvMσ : (vsub : G) ∈ OddOrder.BG.Ch3.S10.Msigma N := Subgroup.mem_subgroupOf.mp hvsub
      have haM₂ : (asub : G) ∈ M₂ :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hasub)).1
      have hcva : (vsub : G) * (asub : G) = c := by
        have := congrArg (Subgroup.subtype N) hva; simpa using this
      -- `conj v • M₂ = L` (as `a ∈ M₂`).
      have hvL : MulAut.conj (vsub : G) • M₂ = L := by
        have ha_fix : MulAut.conj (asub : G) • M₂ = M₂ :=
          conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer haM₂)
        rw [← hcL, ← hcva, map_mul, mul_smul, ha_fix]
      -- `x⁻¹vx ∈ N_σ`; `conj (x⁻¹vx) • M₂ = conj v • M₂` (uses `x∈M₂`, `x∈L`).
      have hconjMσ : x⁻¹ * (vsub : G) * x ∈ OddOrder.BG.Ch3.S10.Msigma N := by
        have h := hMσNnormal.conj_mem vsub hvsub (⟨x, hxN⟩⁻¹)
        have := Subgroup.mem_subgroupOf.mp h; simpa using this
      have hkey :
          MulAut.conj (x⁻¹ * (vsub : G) * x) • M₂ = MulAut.conj (vsub : G) • M₂ := by
        have hxM₂ : MulAut.conj x • M₂ = M₂ :=
          conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxM₂mem)
        have hxL : MulAut.conj x⁻¹ • L = L :=
          conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (L.inv_mem hxLmem))
        calc MulAut.conj (x⁻¹ * (vsub : G) * x) • M₂
            = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • (MulAut.conj x • M₂)) := by
              rw [map_mul, map_mul, mul_smul, mul_smul]
          _ = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • M₂) := by rw [hxM₂]
          _ = MulAut.conj x⁻¹ • L := by rw [hvL]
          _ = L := hxL
          _ = MulAut.conj (vsub : G) • M₂ := hvL.symm
      have hmemNM : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ Subgroup.normalizer M₂ := by
        apply mem_normalizer_of_conj_smul_eq_self
        rw [map_mul, mul_smul, hkey, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have hmemMσ : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ OddOrder.BG.Ch3.S10.Msigma N :=
        (OddOrder.BG.Ch3.S10.Msigma N).mul_mem
          ((OddOrder.BG.Ch3.S10.Msigma N).inv_mem hvMσ) hconjMσ
      have hmem1 : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) = 1 := by
        have hinbot : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ (⊥ : Subgroup G) := by
          rw [← hsigmaInf₂]
          exact Subgroup.mem_inf.mpr ⟨hmemMσ,
            Subgroup.mem_inf.mpr ⟨hN_M₂_le hmemNM, hMσN_le hmemMσ⟩⟩
        exact Subgroup.mem_bot.mp hinbot
      have hvx : x⁻¹ * (vsub : G) * x = (vsub : G) := (inv_mul_eq_one.mp hmem1).symm
      have hvCx : (vsub : G) ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy; rw [Set.mem_singleton_iff.mp hy]
        have hcomm : x * (vsub : G) = (vsub : G) * x := by nth_rewrite 1 [← hvx]; group
        exact hcomm
      -- Existence + uniqueness of `r ∈ R(x)` with `conj r • M₂ = L`.
      refine ⟨(vsub : G), ⟨Subgroup.mem_inf.mpr ⟨hvMσ, hvCx⟩, hvL⟩, ?_⟩
      rintro r ⟨hrR, hrL⟩
      obtain ⟨hrMσ, _hrCx⟩ := Subgroup.mem_inf.mp hrR
      have hconj_eq : MulAut.conj ((vsub : G)⁻¹ * r) • M₂ = M₂ := by
        rw [map_mul, mul_smul, hrL, ← hvL, ← mul_smul, ← map_mul, inv_mul_cancel,
          map_one, one_smul]
      have hmemN' : (vsub : G)⁻¹ * r ∈ Subgroup.normalizer M₂ :=
        mem_normalizer_of_conj_smul_eq_self hconj_eq
      have hmemMσ' : (vsub : G)⁻¹ * r ∈ OddOrder.BG.Ch3.S10.Msigma N :=
        (OddOrder.BG.Ch3.S10.Msigma N).mul_mem
          ((OddOrder.BG.Ch3.S10.Msigma N).inv_mem hvMσ) hrMσ
      have hbot' : (vsub : G)⁻¹ * r ∈ (⊥ : Subgroup G) := by
        rw [← hsigmaInf₂]
        exact Subgroup.mem_inf.mpr ⟨hmemMσ',
          Subgroup.mem_inf.mpr ⟨hN_M₂_le hmemN', hMσN_le hmemMσ'⟩⟩
      exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot')).symm
  · -- Uniqueness: any qualifying `N'` lies in `ℳ(C_G(x)) = {N}`.
    intro N' hN'
    have hmem : N' ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hN'.1, hN'.2.1⟩
    rw [hsingleton] at hmem
    exact Set.mem_singleton_iff.mp hmem

/-- **σ-classes are equal or disjoint** (BG §1 partition, mmd L3789): if two maximal subgroups
share a `σ`-prime then their `σ`-sets coincide.  Combines Theorem 13.9 (nonconjugate ⟹ disjoint
`σ`) with the conjugation-equivariance of `σ` (`sigma_conj`).  This is the partition property the
`σ`-decomposition rests on; used to match the `σ`-factors of an element in Lemma 14.5(a). -/
theorem sigma_eq_of_mem_sigma_of_mem_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M M' : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hM' : M' ∈ maximalSubgroups G) {p : ℕ}
    (hpM : p ∈ OddOrder.BG.Ch3.S10.sigma M) (hpM' : p ∈ OddOrder.BG.Ch3.S10.sigma M') :
    OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma M' := by
  -- `M`, `M'` are conjugate (else Theorem 13.9 makes their `σ`-sets disjoint).
  obtain ⟨g, rfl⟩ : IsConjugateSubgroup M M' := by
    by_contra hnc
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hM' hnc) hpM hpM'
  ext q
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · haveI : Fact q.Prime :=
      ⟨Nat.prime_of_mem_primeFactors ((OddOrder.BG.Ch3.S10.mem_sigma_iff M q).mp hq).1⟩
    exact OddOrder.BG.Ch3.S10.sigma_conj g hq
  · haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors
      ((OddOrder.BG.Ch3.S10.mem_sigma_iff (MulAut.conj g • M) q).mp hq).1⟩
    have h := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hq
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h

/-- **Every prime divides some `σ(M)`** (BG §1, mmd L3789): for a prime `p ∣ |G|` there is a
maximal subgroup `M` with `p ∈ σ(M)`.  A Sylow `p`-subgroup `P` of `G` is non-normal (else `G`
would be a `p`-group, hence solvable, against `hG.notSolvable`), so `N_G(P)` lies in a maximal `M`;
then `P` is a Sylow `p`-subgroup of `M` whose `G`-normalizer `N_G(P) ≤ M`, which is exactly
`p ∈ σ(M)`.  Foundation for the σ-decomposition (every nonidentity element has a `σ`-piece). -/
theorem exists_mem_sigma_of_prime_dvd_card [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G) :
    ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M := by
  classical
  haveI : IsSimpleGroup G := hG.simple
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P.card_eq_multiplicity
  have hfactG : (Nat.card G).factorization p ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Fact.out (Nat.card_pos).ne' hpG).ne'
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hpG
  have hNne : Subgroup.normalizer ((P : Subgroup G) : Set G) ≠ ⊤ := by
    intro hN_top
    have hPnormal : (P : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp hN_top
    rcases hPnormal.eq_bot_or_eq_top with hb | ht
    · exact hPne hb
    · refine hG.notSolvable ?_
      have hPG : IsPGroup p G := by
        have he : IsPGroup p ↥(⊤ : Subgroup G) := ht ▸ P.isPGroup'
        exact he.of_equiv Subgroup.topEquiv
      haveI := hPG.isNilpotent
      infer_instance
  obtain ⟨M, hMco, hNM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
  have hpP : p ∣ Nat.card ↥(P : Subgroup G) := by
    rw [hPcard]; exact dvd_pow_self p hfactG
  have hpdvdM : p ∣ Nat.card ↥M := hpP.trans (Subgroup.card_dvd_of_le hPM)
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, (Nat.card_pos).ne'⟩
  refine ⟨M, hM, ?_⟩
  rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
  refine ⟨hpM, ?_⟩
  -- `P` is a Sylow `p`-subgroup of `M` (the `p`-parts of `|M|` and `|G|` agree).
  have hmap : ((P : Subgroup G).subgroupOf M).map M.subtype = (P : Subgroup G) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM]
  have hcardPM : Nat.card ↥((P : Subgroup G).subgroupOf M) = Nat.card ↥(P : Subgroup G) := by
    have h := Nat.card_congr (Subgroup.equivMapOfInjective
      ((P : Subgroup G).subgroupOf M) M.subtype M.subtype_injective).toEquiv
    rwa [hmap] at h
  have hfacteq : (Nat.card G).factorization p = (Nat.card ↥M).factorization p := by
    refine le_antisymm ?_ ?_
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos).ne', ← hPcard]
      exact Subgroup.card_dvd_of_le hPM
    · exact (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (Nat.card_pos).ne').mpr
        (Subgroup.card_subgroup_dvd_card M) p
  have hQcard : Nat.card ↥((P : Subgroup G).subgroupOf M)
      = p ^ (Nat.card ↥M).factorization p := by rw [hcardPM, hPcard, hfacteq]
  refine ⟨Sylow.ofCard ((P : Subgroup G).subgroupOf M) hQcard, ?_⟩
  rw [Sylow.coe_ofCard, hmap]
  exact hNM

/-- **BG `ell_sigma0P`** (Coq BGsection14:222): the genuine σ-length of `x` is `0` iff `x = 1`.
If `x ≠ 1`, any prime `p ∣ orderOf x` divides `|G|`, hence is a `σ`-prime of some maximal `M`
(`exists_mem_sigma_of_prime_dvd_card`); then `sigmaPart M x ≠ 1` (else `x` would be a `σ(M)′`-element
avoiding `p`), so `sigma_decomposition x` is nonempty.  (Placed after
`exists_mem_sigma_of_prime_dvd_card`, which it cites; the genuine `sigmaLength` is defined earlier.) -/
theorem sigmaLength_eq_zero_iff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (x : G) :
    sigmaLength x = 0 ↔ x = 1 := by
  rw [sigmaLength, Set.ncard_eq_zero (Set.toFinite _)]
  constructor
  · intro hempty
    by_contra hx1
    have hox : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hox
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨M, hMmax, hpσ⟩ :=
      exists_mem_sigma_of_prime_dvd_card hG (hpdvd.trans (orderOf_dvd_natCard x))
    have hne : sigmaPart M x ≠ 1 := by
      intro hcontra
      have hcompl : IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x :=
        isPiElement_compl_of_piPart_eq_one hcontra
      exact (hcompl p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos x).ne'⟩)) hpσ
    have hmem : sigmaPart M x ∈ sigmaDecomposition x := by
      refine ⟨⟨M, hMmax, rfl⟩, ?_⟩
      simp only [Set.mem_singleton_iff]; exact hne
    rw [hempty] at hmem
    exact Set.notMem_empty _ hmem
  · rintro rfl
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨M, hMmax, rfl⟩, hy⟩
    exact hy (by simp [sigmaPart, piPart_one])

/-- **σ-decomposition keystone** (BG §1, mmd L3793): a nonidentity `σ(M)`-element `x` has
`ℓ_σ(x) = 1`.  The cyclic group `⟨x⟩` is a nonidentity proper `σ(M)`-subgroup (proper since `G` is
non-solvable, hence non-cyclic), so by Corollary 12.16(a)
(`sigma_subgroup_conj_into_Msigma_general`) it is `G`-conjugate into `M_σ`; thus a conjugate of `M`
is a `σ`-maximal of `x`, giving `𝓜_σ(x) ≠ ∅`.  This is the existence half of the σ-decomposition
that drives Lemma 14.6 (extracting a `σ`-length-one factor of an element). -/
theorem exists_mem_Msigma_of_isPiElement_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ≠ 1) (hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) :
    (maximalSigmaSubgroupsOfElement x).Nonempty := by
  have hclosne : Subgroup.closure ({x} : Set G) ≠ ⊥ := fun h =>
    hx (Subgroup.mem_bot.mp (h ▸ Subgroup.subset_closure (Set.mem_singleton x)))
  have hlt : Subgroup.closure ({x} : Set G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hG.notSolvable (isSolvable_of_comm fun a b => ?_))
    have hmem : ∀ y : G, y ∈ Subgroup.zpowers x := fun y => by
      rw [Subgroup.zpowers_eq_closure, htop]; exact Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := hmem a
    obtain ⟨n, rfl⟩ := hmem b
    rw [← zpow_add, ← zpow_add, Int.add_comm]
  have hxpisub : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      (Subgroup.closure ({x} : Set G)) := fun p hp =>
    hxpi p (by rwa [← Subgroup.zpowers_eq_closure, Nat.card_zpowers] at hp)
  obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hM hclosne hlt hxpisub
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM hN hnc)
  refine ⟨MulAut.conj g⁻¹ • M, mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g⁻¹, rfl⟩, ?_⟩
  rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have he : (MulAut.conj g⁻¹)⁻¹ • x = MulAut.conj g • x := by
    rw [← map_inv (MulAut.conj) g⁻¹, inv_inv]
  rw [he]
  exact hg (Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _
    (Subgroup.subset_closure (Set.mem_singleton x)))

/-- The scaffold form: a nonidentity `σ(M)`-element `x` has `D.length x = 1` (it cites the genuine
existence half `exists_mem_Msigma_of_isPiElement_sigma` through `D.length_one_iff`). -/
theorem length_one_of_isPiElement_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ≠ 1) (hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) :
    D.length x = 1 :=
  (D.length_one_iff x).mpr ⟨hx, exists_mem_Msigma_of_isPiElement_sigma hG hM hx hxpi⟩

/-- **BG `ell_sigma1P`** (Coq BGsection14:272): `sigmaLength x = 1 ↔ x ≠ 1 ∧ 𝓜_σ(x) ≠ ∅`.  This is
*exactly* the characterization the `SigmaDecompositionData` scaffold posits as `length_one_iff`,
here **proved** for the genuine `sigmaLength`.  ⟸ is `Msigma_ell1`.  ⟹: a σ-length-`1` element has
all its primes in one `σ(M₀)` (each prime `p ∣ |x|` lands in some `σ(L)`, forcing the nonidentity
`sigmaPart L x` to equal the unique block `y = sigmaPart M₀ x`, so `p ∈ π(y) ⊆ σ(M₀)`), hence is a
`σ(M₀)`-element, and the existence half `exists_mem_Msigma_of_isPiElement_sigma` finishes. -/
theorem sigmaLength_eq_one_iff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (x : G) :
    sigmaLength x = 1 ↔ x ≠ 1 ∧ (maximalSigmaSubgroupsOfElement x).Nonempty := by
  constructor
  · intro hlen
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, (sigmaLength_eq_zero_iff hG 1).mpr rfl] at hlen
      exact zero_ne_one hlen
    refine ⟨hx1, ?_⟩
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hlen
    have hyMem : y ∈ sigmaDecomposition x := by rw [hy]; rfl
    obtain ⟨⟨M₀, hM₀, hy_eq⟩, hyne⟩ := hyMem
    have hxσ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M₀) x := by
      intro p hp
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      obtain ⟨L, hL, hpL⟩ := exists_mem_sigma_of_prime_dvd_card hG
        ((Nat.dvd_of_mem_primeFactors hp).trans (orderOf_dvd_natCard x))
      have hLne : sigmaPart L x ≠ 1 := fun hc =>
        isPiElement_compl_of_piPart_eq_one hc p hp hpL
      have hLmem : sigmaPart L x ∈ sigmaDecomposition x :=
        ⟨⟨L, hL, rfl⟩, by simp only [Set.mem_singleton_iff]; exact hLne⟩
      rw [hy, Set.mem_singleton_iff] at hLmem
      have hpy : p ∣ orderOf (sigmaPart M₀ x) := by
        rw [← hy_eq, ← hLmem]
        exact prime_dvd_orderOf_piPart (Nat.prime_of_mem_primeFactors hp) hpL
          (Nat.dvd_of_mem_primeFactors hp)
      exact isPiElement_piPart (OddOrder.BG.Ch3.S10.sigma M₀) x p
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpy, (orderOf_pos _).ne'⟩)
    exact exists_mem_Msigma_of_isPiElement_sigma hG hM₀ hx1 hxσ
  · rintro ⟨hx1, M, hM, hxM⟩
    exact Msigma_ell1 hG hM hxM hx1

/-- The **genuine** `SigmaDecompositionData`: `length := sigmaLength` (the honestly constructed
σ-length) with `length_one_iff` discharged by `sigmaLength_eq_one_iff` (Coq `ell_sigma1P`).  This
*realizes* the carrier the scaffold only posited — downstream consumers can be fed this in place of
`dummySigmaDecomposition` ([[scaffold-sorry-free-not-done]]: the posited interface is constructible). -/
noncomputable def genuineSigmaDecomposition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) : SigmaDecompositionData G where
  length := sigmaLength
  length_one_iff := sigmaLength_eq_one_iff hG

/-- **`pi_of_cent_sigma` τ₂-case `ℓ_σ = 1`** (Coq `BGsection14`:809-821): a nonidentity
`τ₂(M)`-element `x'` has `ℓ_σ(x') = 1`.  Following BG: a `τ₂(M)`-prime `p ∣ |x'|` gives a rank-two
elementary abelian `A ≤ E` (`exists_elemAb_rank_two_le_E_of_tau2`); a maximal `N ⊇ N_G(A)` then
absorbs every `τ₂(M)`-prime into `σ(N)` (`tau2_prime_mem_sigma_diff_beta`), so `x'` is a
`σ(N)`-element and `length_one_of_isPiElement_sigma`/`exists_mem_Msigma_of_isPiElement_sigma` gives
`ℓ_σ(x') = 1`.  This is the second discharged part of `pi_of_cent_sigma`'s τ₂ branch (with
`pi_of_cent_sigma_tau2_uniqueness`). -/
theorem tau2_element_sigmaLength_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x' : G} (hx'1 : x' ≠ 1)
    (hx'τ2 : ∀ p ∈ piSet (Subgroup.closure ({x'} : Set G)), p ∈ tau2 M) :
    sigmaLength x' = 1 := by
  classical
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have hcard : Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  -- `piSet (closure {x'})` membership reduces to `(orderOf x').primeFactors`.
  have hpiSet : ∀ q : ℕ, q ∈ (orderOf x').primeFactors → q ∈ tau2 M := fun q hq =>
    hx'τ2 q (by
      show q ∈ (Nat.card ↥(Subgroup.closure ({x'} : Set G))).primeFactors
      rw [hcard]; exact hq)
  -- a `τ₂(M)`-prime `p ∣ |x'|`, and a rank-two `τ₂(M)` elementary abelian `A ≤ E`.
  have hord_ne : orderOf x' ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨p, hp_prime, hp_dvd⟩ := (orderOf x').exists_prime_and_dvd hord_ne
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hpτ2 : p ∈ tau2 M :=
    hpiSet p (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, (orderOf_pos x').ne'⟩)
  obtain ⟨A, hAea, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetup hpτ2
  have hAcard : Nat.card ↥A = p ^ 2 := hAea.2
  have hAne : A ≠ ⊥ := by
    rintro rfl
    rw [show Nat.card ↥(⊥ : Subgroup G) = 1 from by simp] at hAcard
    nlinarith [hp_prime.two_le, hAcard]
  -- a maximal `N ⊇ N_G(A)`.
  obtain ⟨N, hNmem, hN_le⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hAne (hAE.trans hsetup.E_le)
  have hNcontain : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    ⟨mem_maximalSubgroups.mp hNmem, hN_le⟩
  -- every prime of `x'` lands in `σ(N)`, so `x'` is a `σ(N)`-element.
  have hx'σ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N) x' := by
    intro q hq
    haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    exact (tau2_prime_mem_sigma_diff_beta hG hsetup hpτ2 hAea hAE hNcontain
      (Nat.prime_of_mem_primeFactors hq) (hpiSet q hq)).1
  exact (sigmaLength_eq_one_iff hG x').mpr
    ⟨hx'1, exists_mem_Msigma_of_isPiElement_sigma hG hNmem hx'1 hx'σ⟩

/-- **σ-decomposition: extracting a `σ`-length-one factor** (BG §1, mmd L3793): every `g ≠ 1`
factors as `g = x · x'` with `x` a `σ`-length-one element (the `σ(M)`-part for a maximal `M` whose
`σ(M)` contains a prime of `g`), `x'` a `σ(M)′`-element, both in `⟨g⟩` and commuting.  Combines
`exists_mem_sigma_of_prime_dvd_card` (a prime of `g` lies in some `σ(M)`), the two-block
decomposition `exists_isPiElement_mul`, and the keystone `length_one_of_isPiElement_sigma`.  This
is the existence input to Lemma 14.6. -/
theorem exists_length_one_factor [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {g : G} (hg : g ≠ 1) :
    ∃ (x x' : G) (M : Subgroup G), g = x * x' ∧ Commute x x' ∧
      x ∈ Subgroup.zpowers g ∧ x' ∈ Subgroup.zpowers g ∧ D.length x = 1 ∧
      M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x ∧
      OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x' := by
  classical
  obtain ⟨p, hp, hpg⟩ := (orderOf g).exists_prime_and_dvd (fun h => hg (orderOf_eq_one_iff.mp h))
  haveI : Fact p.Prime := ⟨hp⟩
  have hpG : p ∣ Nat.card G := hpg.trans (orderOf_dvd_natCard g)
  obtain ⟨M, hM, hpσM⟩ := exists_mem_sigma_of_prime_dvd_card hG hpG
  obtain ⟨x, x', hmul, hcomm, hxπ, hx'π, hxz, hx'z⟩ :=
    OddOrder.GroupTheory.exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma M) g
  have hx1 : x ≠ 1 := by
    intro hx0
    rw [hx0, one_mul] at hmul
    exact (hx'π p (by
      rw [hmul]; exact Nat.mem_primeFactors.mpr ⟨hp, hpg, (orderOf_pos g).ne'⟩)) hpσM
  exact ⟨x, x', M, hmul.symm, hcomm, hxz, hx'z,
    length_one_of_isPiElement_sigma hG D hM hx1 hxπ, hM, hxπ, hx'π⟩

open Classical in
/-- **BG's `R(x)`** (mmd L3906): the normal Hall subgroup of `C_G(x)` from Theorem 14.4.  When
`ℓ_σ(x) = 1` and `|𝓜_σ(x)| > 1`, `R(x) = N_σ ∩ C_G(x)` for the unique `N = N(x) ∈ 𝓜(C_G(x))`
of Theorem 14.4; otherwise (`x = 1`, `ℓ_σ(x) ≠ 1`, or `|𝓜_σ(x)| = 1`) `R(x) = 1`. -/
noncomputable def Rsub [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (x : G) : Subgroup G :=
  if h : x ≠ 1 ∧ D.length x = 1 ∧ 1 < (maximalSigmaSubgroupsOfElement x).ncard then
    OddOrder.BG.Ch3.S10.Msigma
        (((sigmaLength_one_centralizer_structure hG D h.1 h.2.1).2 h.2.2).exists.choose)
      ⊓ Subgroup.centralizer ({x} : Set G)
  else ⊥

/-- `R(x) ≤ C_G(x)` (immediate from the definition; holds in both branches). -/
theorem Rsub_le_centralizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (x : G) :
    Rsub hG D x ≤ Subgroup.centralizer ({x} : Set G) := by
  rw [Rsub]; split_ifs
  · exact inf_le_right
  · exact bot_le

/-- The defining value of `R(x)` in the multi-maximal case: `R(x) = N_σ ∩ C_G(x)` for the
unique `N` of Theorem 14.4 (`.exists.choose`). -/
theorem Rsub_eq_inf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hx : x ≠ 1) (hlen : D.length x = 1)
    (hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard) :
    Rsub hG D x = OddOrder.BG.Ch3.S10.Msigma
      (((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose)
      ⊓ Subgroup.centralizer ({x} : Set G) := by
  rw [Rsub, dif_pos ⟨hx, hlen, hgt⟩]

/-- **Packaged neighbour data for `R(x)`** (the multi-maximal case): the unique `N = N(x)` of
Theorem 14.4 together with `R(x) = N_σ ∩ C_G(x)`, `C_G(x) ≤ N`, `π(⟨x⟩) ⊆ τ₂(N)`, and the
complement property `M ∩ N` complements `N_σ` in `N` for every `M ∈ 𝓜_σ(x)` (14.4(e)).  This
is the interface consumed by Lemma 14.5(a)/(c) and Lemma 14.6. -/
theorem exists_neighbor_eq_Rsub [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hlen : D.length x = 1)
    (hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      Rsub hG D x = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N) ∧
      (∀ M ∈ maximalSigmaSubgroupsOfElement x,
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          ((M ⊓ N).subgroupOf N)) := by
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  set N := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose with hNdef
  have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
  refine ⟨N, spec.1, spec.2.1, Rsub_eq_inf hG D hx hlen hgt, spec.2.2.2.2.1, fun M hM => ?_⟩
  exact (spec.2.2.2.2.2.2 M hM).2.2.1

/-- **`R(z)` consists of `σ(M)′`-elements** for `M ∈ 𝓜_σ(z)`.  Crux of the σ-factor matching
in Lemma 14.5(a): with `z` a `σ(M)`-element, `g = z·r` (`r ∈ R(z)`) is a `(σ(M), σ(M)′)`-split.
Proof: `r ∈ N_σ` is a `σ(N)`-element (`N = N(z)`); a prime `p ∈ σ(M) ∩ σ(N)` forces
`σ(M) = σ(N)` (partition), but `π(⟨z⟩) ⊆ σ(M) = σ(N)` and `⊆ τ₂(N)` with `τ₂(N) ∩ σ(N) = ∅`
gives `z = 1`. (When `|𝓜_σ(z)| = 1`, `R(z) = 1`, trivially.) -/
theorem isPiElement_sigmaCompl_of_mem_Rsub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {z : G}
    (hlen : D.length z = 1) {M : Subgroup G} (hM : M ∈ maximalSigmaSubgroupsOfElement z)
    {r : G} (hr : r ∈ Rsub hG D z) :
    OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ r := by
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpσM
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement z).ncard
  · obtain ⟨N, hNmax, _, hReq, hπτ2, _⟩ := exists_neighbor_eq_Rsub hG D hlen hgt
    rw [hReq] at hr
    have hrN : r ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hr).1
    -- `p ∈ σ(N)` since `r ∈ N_σ`.
    have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans
            ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hrN),
          Nat.card_pos.ne'⟩)
    -- `σ(M) = σ(N)` since they share `p`.
    have hσeq : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma N :=
      sigma_eq_of_mem_sigma_of_mem_sigma hG hM.1 hNmax hpσM hpσN
    -- A prime `q ∣ |z|` lies in `σ(M)=σ(N)` and `τ₂(N)`, against `τ₂(N) ⊆ σ(N)ᶜ`.
    have hz1 : z ≠ 1 := ((D.length_one_iff z).mp hlen).1
    obtain ⟨q, hqp, hqdvd⟩ :=
      (orderOf z).exists_prime_and_dvd (fun h => hz1 (orderOf_eq_one_iff.mp h))
    have hcardz : Nat.card ↥(Subgroup.closure ({z} : Set G)) = orderOf z := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    have hqπ : q ∈ piSet (Subgroup.closure ({z} : Set G)) := by
      rw [piSet, Set.mem_setOf_eq, hcardz]
      exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos z).ne'⟩
    have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
        ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hM.2),
          Nat.card_pos.ne'⟩)
    rw [hσeq] at hqσM
    exact tau2_subset_sigma_compl N (hπτ2 q hqπ) hqσM
  · rw [Rsub, dif_neg (fun h => hgt h.2.2), Subgroup.mem_bot] at hr
    rw [hr, orderOf_one, Nat.primeFactors_one] at hp
    simp at hp

/-- **Sharp transitivity ⟹ `|R(x)| = |𝓜_σ(x)|`** (BG Theorem 14.4 headline): `R(x) = N_σ ∩ C_G(x)`
acts *regularly* on `𝓜_σ(x)` by conjugation (`r ↦ M₀ʳ`), so the two have equal cardinality.  In the
single-maximal case both sides equal `1` (`R(x) = 1`, `|𝓜_σ(x)| = 1`).  This is the per-element
input to the double count of Lemma 14.5(c). -/
theorem Rsub_ncard_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hlen : D.length x = 1) :
    Nat.card ↥(Rsub hG D x) = (maximalSigmaSubgroupsOfElement x).ncard := by
  classical
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  have hne : (maximalSigmaSubgroupsOfElement x).Nonempty := ((D.length_one_iff x).mp hlen).2
  have hfin : (maximalSigmaSubgroupsOfElement x).Finite := Set.toFinite _
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · -- Multi-maximal: the orbit map `r ↦ M₀ʳ` is a bijection `R(x) ≃ 𝓜_σ(x)` by sharp transitivity.
    obtain ⟨M0, hM0⟩ := hne
    have hReq : Rsub hG D x =
        OddOrder.BG.Ch3.S10.Msigma
          (((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose)
          ⊓ Subgroup.centralizer ({x} : Set G) :=
      Rsub_eq_inf hG D hx hlen hgt
    have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
    have hsharp := (spec.2.2.2.2.2.2 M0 hM0).2.2.2
    have hmem : ∀ r ∈ Rsub hG D x, MulAut.conj r • M0 ∈ maximalSigmaSubgroupsOfElement x := by
      intro r hr
      have hrC : r ∈ Subgroup.centralizer ({x} : Set G) := Rsub_le_centralizer hG D x hr
      have hrx : r * x = x * r := (Subgroup.mem_centralizer_iff.mp hrC x rfl).symm
      refine ⟨mem_maximalSubgroups_of_isConjugateSubgroup hM0.1 ⟨r, rfl⟩, ?_⟩
      rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hxfix : (MulAut.conj r)⁻¹ • x = x := by
        have h1 : (MulAut.conj r)⁻¹ • x = r⁻¹ * x * r := by
          rw [← map_inv (MulAut.conj) r, MulAut.smul_def, MulAut.conj_apply, inv_inv]
        rw [h1, mul_assoc, ← hrx, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hxfix]; exact hM0.2
    -- The forward orbit map (into `𝓜_σ(x)`) and its bijectivity.
    have hpred : ∀ r ∈ Rsub hG D x,
        r ∈ OddOrder.BG.Ch3.S10.Msigma
          (((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose)
          ⊓ Subgroup.centralizer ({x} : Set G) := fun r hr => hReq ▸ hr
    let f : ↥(Rsub hG D x) → ↥(maximalSigmaSubgroupsOfElement x) :=
      fun r => ⟨MulAut.conj (r : G) • M0, hmem r r.2⟩
    have hbij : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro ⟨r1, hr1⟩ ⟨r2, hr2⟩ heq
        have hL : MulAut.conj r1 • M0 = MulAut.conj r2 • M0 := congrArg Subtype.val heq
        exact Subtype.ext
          ((hsharp (MulAut.conj r1 • M0) (hmem r1 hr1)).unique
            ⟨hpred r1 hr1, rfl⟩ ⟨hpred r2 hr2, hL.symm⟩)
      · rintro ⟨L, hL⟩
        obtain ⟨r, hrpred, -⟩ := hsharp L hL
        exact ⟨⟨r, hReq ▸ hrpred.1⟩, Subtype.ext hrpred.2⟩
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.ofBijective f hbij)
  · -- Single-maximal: `R(x) = 1` and `|𝓜_σ(x)| = 1`.
    have hpos : 0 < (maximalSigmaSubgroupsOfElement x).ncard := by
      rw [Set.ncard_pos hfin]; exact hne
    have h1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 := by omega
    rw [h1, Rsub, dif_neg (fun h => hgt h.2.2)]
    simp

/-- **BG Lemma 14.5(a)** (mmd L3919): for distinct `σ`-length-one elements `x`, `y`, the cosets
`x R(x)` and `y R(y)` are disjoint.  Proof (s-part-free, via the two-block decomposition):
`g = x·x'` makes `x` the `σ(M_x)`-part of `g`, `g = y·y''` makes `y` the `σ(M_y)`-part.  If the
`σ`-classes agree, `x = y` (contradiction); otherwise some prime of `y` forces `σ(M_y) = σ(N_x)`,
so `x' = y` and `x = y''`, and then Theorem 14.4(e) (`N_y ∩ N_x` complements `(N_x)_σ`) gives
`y ∈ (N_x)_σ ∩ N_y = 1`, a contradiction. -/
theorem xRsub_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x y : G} (hx : D.length x = 1) (hy : D.length y = 1)
    (hxy : x ≠ y) :
    Disjoint {g : G | ∃ r ∈ Rsub hG D x, g = x * r}
      {g : G | ∃ r ∈ Rsub hG D y, g = y * r} := by
  classical
  rw [Set.disjoint_left]
  rintro g ⟨x', hx'R, rfl⟩ ⟨y'', hy''R, hg2⟩
  -- `g = x · x'`, and `hg2 : x · x' = y · y''`.
  have hx1 : x ≠ 1 := ((D.length_one_iff x).mp hx).1
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hy).1
  obtain ⟨M_x, hMxmax, hxMx⟩ := ((D.length_one_iff x).mp hx).2
  obtain ⟨M_y, hMymax, hyMy⟩ := ((D.length_one_iff y).mp hy).2
  -- `x` is a `σ(M_x)`-element, `y` a `σ(M_y)`-element.
  have hxPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) x := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M_x p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans
          ((OddOrder.BG.Ch3.S10.Msigma M_x).orderOf_dvd_natCard hxMx),
        Nat.card_pos.ne'⟩)
  have hyPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y) y := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M_y p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans
          ((OddOrder.BG.Ch3.S10.Msigma M_y).orderOf_dvd_natCard hyMy),
        Nat.card_pos.ne'⟩)
  -- `x'` is a `σ(M_x)′`-element, `y''` a `σ(M_y)′`-element (the crux building block).
  have hx'Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hx ⟨hMxmax, hxMx⟩ hx'R
  have hy''Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y)ᶜ y'' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hy ⟨hMymax, hyMy⟩ hy''R
  -- `x` commutes with `x'`, `y` with `y''`.
  have hcx : Commute x x' :=
    Subgroup.mem_centralizer_iff.mp (Rsub_le_centralizer hG D x hx'R) x (Set.mem_singleton x)
  have hcy : Commute y y'' :=
    Subgroup.mem_centralizer_iff.mp (Rsub_le_centralizer hG D y hy''R) y (Set.mem_singleton y)
  by_cases hσeq : OddOrder.BG.Ch3.S10.sigma M_x = OddOrder.BG.Ch3.S10.sigma M_y
  · -- **Equal classes**: both decompositions are `(σ(M_x), σ(M_x)′)`, so `x = y`.
    have ha2 : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) y := by
      rw [hσeq]; exact hyPi
    have hb2 : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ y'' := by
      rw [hσeq]; exact hy''Pi
    exact hxy (OddOrder.GroupTheory.isPiElement_mul_unique rfl hcx hxPi hx'Pi
      hg2.symm hcy ha2 hb2).1
  · -- **Disjoint classes**: `σ(M_x) ∩ σ(M_y) = ∅`.
    have hdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M_x) (OddOrder.BG.Ch3.S10.sigma M_y) :=
      Set.disjoint_left.mpr fun p hpx hpy =>
        hσeq (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hMymax hpx hpy)
    -- `x` is a `σ(M_y)′`-element (disjoint).
    have hxPiCompl : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y)ᶜ x := by
      intro p hp
      exact fun hpy => Set.disjoint_left.mp hdisj (hxPi p hp) hpy
    -- `π(g) = π(x) ∪ π(x')` (coprime commuting factors).
    have hcox : Nat.Coprime (orderOf x) (orderOf x') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hxPi hx'Pi
    have hpg : (orderOf (x * x')).primeFactors =
        (orderOf x).primeFactors ∪ (orderOf x').primeFactors := by
      rw [hcx.orderOf_mul_eq_mul_orderOf_of_coprime hcox,
        Nat.primeFactors_mul (orderOf_pos x).ne' (orderOf_pos x').ne']
    -- `π(y) ⊆ π(g)` (`y` is a factor of `g`).
    have hcoy : Nat.Coprime (orderOf y) (orderOf y'') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hyPi hy''Pi
    have hyg : (orderOf y).primeFactors ⊆ (orderOf (x * x')).primeFactors := by
      rw [hg2, hcy.orderOf_mul_eq_mul_orderOf_of_coprime hcoy,
        Nat.primeFactors_mul (orderOf_pos y).ne' (orderOf_pos y'').ne']
      exact Finset.subset_union_left
    -- `y ≠ 1` gives a prime `p ∈ π(y)`.
    obtain ⟨p, hpy⟩ : (orderOf y).primeFactors.Nonempty := by
      apply Nat.nonempty_primeFactors.mpr
      have h0 := orderOf_pos y
      have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
      omega
    have hpσMy : p ∈ OddOrder.BG.Ch3.S10.sigma M_y := hyPi p hpy
    -- `|𝓜_σ(x)| > 1`: else `x' = 1` and `p ∈ π(x) ⊆ σ(M_x)`, forcing `σ(M_x) = σ(M_y)`.
    by_cases hgtx : 1 < (maximalSigmaSubgroupsOfElement x).ncard
    · -- **Main case.**
      obtain ⟨N_x, hNxmax, _, hReqx, hπτ2x, hcomplx⟩ := exists_neighbor_eq_Rsub hG D hx hgtx
      have hx'Nx : x' ∈ OddOrder.BG.Ch3.S10.Msigma N_x := by
        rw [hReqx] at hx'R; exact (Subgroup.mem_inf.mp hx'R).1
      have hx'PiNx : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N_x) x' :=
        fun q hq => OddOrder.BG.Ch3.S10.Msigma_isPiGroup N_x q (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hq,
            (Nat.dvd_of_mem_primeFactors hq).trans
              ((OddOrder.BG.Ch3.S10.Msigma N_x).orderOf_dvd_natCard hx'Nx),
            Nat.card_pos.ne'⟩)
      -- `p ∈ π(x) ∪ π(x')`; the `π(x)` case is impossible, so `σ(M_y) = σ(N_x)`.
      have hpmem : p ∈ (orderOf x).primeFactors ∪ (orderOf x').primeFactors := hpg ▸ hyg hpy
      have hσMyNx : OddOrder.BG.Ch3.S10.sigma M_y = OddOrder.BG.Ch3.S10.sigma N_x := by
        rcases Finset.mem_union.mp hpmem with hpx | hpx'
        · exact absurd
            (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hMymax (hxPi p hpx) hpσMy) hσeq
        · exact sigma_eq_of_mem_sigma_of_mem_sigma hG hMymax hNxmax hpσMy (hx'PiNx p hpx')
      -- Hence `x'` is a `σ(M_y)`-element; `g = x'·x` is a `(σ(M_y), σ(M_y)′)`-split.
      have hx'PiMy : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y) x' := by
        rw [hσMyNx]; exact hx'PiNx
      obtain ⟨hx'y, hxy''⟩ := OddOrder.GroupTheory.isPiElement_mul_unique
        (g := x * x') hcx.symm hcx.symm hx'PiMy hxPiCompl hg2.symm hcy hyPi hy''Pi
      -- `x'=y`, `x=y''`; then `N_y ∈ 𝓜_σ(x)` and 14.4(e) give the contradiction.
      have hy_in_NxSigma : y ∈ OddOrder.BG.Ch3.S10.Msigma N_x := hx'y ▸ hx'Nx
      -- `x = y'' ∈ R(y) ⊆ (N_y)_σ`, so `|𝓜_σ(y)| > 1` and `N_y ∈ 𝓜_σ(x)`.
      have hgty : 1 < (maximalSigmaSubgroupsOfElement y).ncard := by
        by_contra h
        rw [Rsub, dif_neg (fun hc => h hc.2.2), Subgroup.mem_bot] at hy''R
        exact hx1 (hxy''.trans hy''R)
      obtain ⟨N_y, hNymax, hCyNy, hReqy, _, _⟩ := exists_neighbor_eq_Rsub hG D hy hgty
      have hx_in_NySigma : x ∈ OddOrder.BG.Ch3.S10.Msigma N_y := by
        rw [hReqy] at hy''R
        rw [hxy'']; exact (Subgroup.mem_inf.mp hy''R).1
      have hNy_mem : N_y ∈ maximalSigmaSubgroupsOfElement x := ⟨hNymax, hx_in_NySigma⟩
      -- Theorem 14.4(e) for `x` with `M = N_y`: `N_y ∩ N_x` complements `(N_x)_σ` in `N_x`.
      -- `y ∈ (N_x)_σ ∩ (N_y ∩ N_x)`, but the complement makes that trivial; so `y = 1`.
      have hcompl := hcomplx N_y hNy_mem
      have hyNx : y ∈ N_x := (OddOrder.BG.Ch3.S10.Msigma_le N_x) hy_in_NxSigma
      have hyNy : y ∈ N_y := hCyNy (Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz])
      have hmem : (⟨y, hyNx⟩ : ↥N_x) ∈
          (OddOrder.BG.Ch3.S10.Msigma N_x).subgroupOf N_x ⊓ (N_y ⊓ N_x).subgroupOf N_x := by
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact ⟨hy_in_NxSigma, Subgroup.mem_inf.mpr ⟨hyNy, hyNx⟩⟩
      have hd := hcompl.disjoint
      rw [disjoint_iff] at hd
      rw [hd, Subgroup.mem_bot] at hmem
      exact hy1 (by simpa using congrArg (Subgroup.subtype N_x) hmem)
    · -- single-maximal case (`x' = 1`, `g = x`): forces `σ(M_x) = σ(M_y)`, a contradiction.
      rw [Rsub, dif_neg (fun hc => hgtx hc.2.2), Subgroup.mem_bot] at hx'R
      rw [hx'R, mul_one] at hpg hyg
      have hpmem : p ∈ (orderOf x).primeFactors := by
        have := hyg hpy
        rwa [hpg, orderOf_one, Nat.primeFactors_one, Finset.union_empty] at this
      exact hσeq (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hMymax (hxPi p hpmem) hpσMy)

/-- **BG's `M̃`** (mmd L3908): `{ x x' | x ∈ M_σ^#, x' ∈ R(x) }`, the `σ`-decompositions of
length `≤ 2` with leading factor in `M_σ^#`.  This is the genuine BG `M̃` (it adjoins the
`ℓ_σ = 2` twisted elements `x x'` that the under-approximation `sigmaSharp` omits). -/
def Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    (M : Subgroup G) : Set G :=
  {g | ∃ x ∈ sigmaSharp M, ∃ x' ∈ Rsub hG D x, g = x * x'}

/-- **Easy half of the `M̃` cover** (`M_σ^# ⊆ M̃`): every `σ`-length-one element `x ∈ M_σ^#` lies in
`M̃` via the trivial decomposition `x = x · 1` (`1 ∈ R(x)`).  This is the `ℓ_σ = 1` part of the
faithful covering (BG Cor 14.9); the `ℓ_σ = 2` twisted elements need the signalizer capture
(Lemma 14.6). -/
theorem sigmaSharp_subset_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} :
    sigmaSharp M ⊆ Mtilde hG D M :=
  fun g hg => ⟨g, hg, 1, Subgroup.one_mem _, (mul_one g).symm⟩

/-- **Signalizer branch ⟹ `M̃` membership** (the bridge from BG's `sigma_decomposition_dichotomy`
first branch to the cover): if `x ∈ M_σ^#` and `x⁻¹ g ∈ R(x)`, then `g = x · (x⁻¹ g) ∈ x R(x) ⊆ M̃`.
This is the coset-to-`M̃` step used to turn the dichotomy's signalizer branch into a cover. -/
theorem mem_Mtilde_of_mem_coset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} {x g : G}
    (hx : x ∈ sigmaSharp M) (hg : x⁻¹ * g ∈ Rsub hG D x) :
    g ∈ Mtilde hG D M :=
  ⟨x, hx, x⁻¹ * g, hg, by group⟩

/-- **BG Lemma 14.5(b)** (mmd L3920), faithful `M̃` form: for nonconjugate maximal `M₁`, `M₂`,
the sets `M̃₁`, `M̃₂` are disjoint.  Immediate from 14.5(a): if `g = x·x' = w·w'` with
`x ∈ (M₁)_σ^#`, `w ∈ (M₂)_σ^#`, then `x ≠ w` (else `x` is a nonidentity element of
`σ(M₁) ∩ σ(M₂) = ∅`), so `g ∈ x R(x) ∩ w R(w) = ∅`. -/
theorem Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ maximalSubgroups G)
    (hM₂ : M₂ ∈ maximalSubgroups G) (hnc : ¬ IsConjugateSubgroup M₁ M₂) :
    Disjoint (Mtilde hG D M₁) (Mtilde hG D M₂) := by
  classical
  rw [Set.disjoint_left]
  rintro g ⟨x, hxsharp, x', hx'R, rfl⟩ ⟨w, hwsharp, w', hw'R, hgw⟩
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    at hxsharp hwsharp
  obtain ⟨hxM₁, hx1⟩ := hxsharp
  obtain ⟨hwM₂, hw1⟩ := hwsharp
  have hlx : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨M₁, hM₁, hxM₁⟩⟩
  have hlw : D.length w = 1 := (D.length_one_iff w).mpr ⟨hw1, ⟨M₂, hM₂, hwM₂⟩⟩
  -- `x ≠ w`: else a prime of `x` lies in `σ(M₁) ∩ σ(M₂) = ∅`.
  have hxw : x ≠ w := by
    rintro rfl
    obtain ⟨p, hp, hpx⟩ :=
      (orderOf x).exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
    have hpσ1 : p ∈ OddOrder.BG.Ch3.S10.sigma M₁ :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₁ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpx.trans ((OddOrder.BG.Ch3.S10.Msigma M₁).orderOf_dvd_natCard hxM₁),
          Nat.card_pos.ne'⟩)
    have hpσ2 : p ∈ OddOrder.BG.Ch3.S10.sigma M₂ :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpx.trans ((OddOrder.BG.Ch3.S10.Msigma M₂).orderOf_dvd_natCard hwM₂),
          Nat.card_pos.ne'⟩)
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM₁ hM₂ hnc) hpσ1 hpσ2
  exact Set.disjoint_left.mp (xRsub_disjoint hG D hlx hlw hxw)
    ⟨x', hx'R, rfl⟩ ⟨w', hw'R, hgw⟩

/-! ### Lemma 14.5(c): the conjugacy-saturation count `|𝒞_G(M̃)| = (|M_σ| − 1)|G:M|` -/

/-- A maximal subgroup of a minimal simple group is self-normalizing (`N_G(M) = M`).  If
`M < N_G(M)` then maximality forces `N_G(M) = ⊤`, i.e. `M ◁ G`, so by simplicity `M = ⊥` or
`M = ⊤`, both excluded (`⊥` is not maximal, `⊤` is not a coatom).  This pins the number of
conjugates of `M` to `[G : M]` (`ncard_conjugates_eq_index_of_normalizer_eq_self`). -/
theorem normalizer_eq_self_of_mem_maximalSubgroups [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer M = M := by
  have hcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with h | h
  · exact h.symm
  · exfalso
    have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hcoatom.2 _ h)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hb | ht
    · exact hG.ne_bot_of_isCoatom hcoatom hb
    · exact hcoatom.1 ht

/-- **Orbit–stabilizer for subgroup conjugation**: when `M` is self-normalizing (`N_G(M) = M`),
the number of conjugates of `M` equals `[G : M]`.  This generalises
`ncard_conjugates_eq_index_of_TI` (which derives `N_G(M) = M` from a TI hypothesis) to any
self-normalizing `M`; the orbit map `g ↦ Mᵍ` factors through `G ⧸ M`. -/
theorem ncard_conjugates_eq_index_of_normalizer_eq_self [Finite G] {M : Subgroup G}
    (hNGM : Subgroup.normalizer M = M) :
    (Set.range (fun g : G => MulAut.conj g • M)).ncard = M.index := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set conjs : Set (Subgroup G) := Set.range (fun g : G => MulAut.conj g • M) with hconjs_def
  let f : G → conjs := fun g => ⟨MulAut.conj g • M, ⟨g, rfl⟩⟩
  have hf_lift : ∀ g₁ g₂ : G, (QuotientGroup.leftRel M) g₁ g₂ → f g₁ = f g₂ := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    have h_in_N : g₁⁻¹ * g₂ ∈ Subgroup.normalizer M := by rw [hNGM]; exact hrel
    have h_conj : MulAut.conj (g₁⁻¹ * g₂) • M = M :=
      Subgroup.conj_smul_eq_self_of_mem (by rw [hNGM] at h_in_N; exact h_in_N)
    ext1
    simp only [f]
    have heq : MulAut.conj g₂ = MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂) := by
      rw [← map_mul]; congr 1; group
    calc (MulAut.conj g₁ • M : Subgroup G)
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • M) := by rw [h_conj]
      _ = (MulAut.conj g₁ * MulAut.conj (g₁⁻¹ * g₂)) • M := by rw [mul_smul]
      _ = MulAut.conj g₂ • M := by rw [← heq]
  let f' : G ⧸ M → conjs := Quotient.lift f (fun a b => hf_lift a b)
  have hf_surj : Function.Surjective f' := by
    rintro ⟨B, g, rfl⟩
    exact ⟨⟦g⟧, rfl⟩
  have hf_inj : Function.Injective f' := by
    rintro ⟨g₁⟩ ⟨g₂⟩ hfeq
    change f g₁ = f g₂ at hfeq
    have hsub : (MulAut.conj g₁ • M : Subgroup G) = MulAut.conj g₂ • M := Subtype.ext_iff.mp hfeq
    have h_step : (MulAut.conj (g₂⁻¹ * g₁) • M : Subgroup G) = M := by
      have heq : MulAut.conj (g₂⁻¹ * g₁) = MulAut.conj g₂⁻¹ * MulAut.conj g₁ := by rw [← map_mul]
      rw [heq, mul_smul, hsub, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have h_mem : g₂⁻¹ * g₁ ∈ Subgroup.normalizer M := by
      rw [Subgroup.mem_normalizer_iff'']
      intro y
      have hmem : y ∈ MulAut.conj (g₂⁻¹ * g₁) • M ↔ y ∈ M := by rw [h_step]
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
      have hcalc : (MulAut.conj (g₂⁻¹ * g₁))⁻¹ • y = (g₂⁻¹ * g₁)⁻¹ * y * (g₂⁻¹ * g₁) := by
        change (MulAut.conj (g₂⁻¹ * g₁)).symm y = _
        rw [MulAut.conj_symm_apply]
      rw [hcalc] at hmem
      exact hmem.symm
    rw [hNGM] at h_mem
    apply Quotient.sound
    change (QuotientGroup.leftRel M) g₁ g₂
    rw [QuotientGroup.leftRel_apply]
    have : (g₂⁻¹ * g₁)⁻¹ ∈ M := M.inv_mem h_mem
    simpa [mul_inv_rev] using this
  have hbij : Function.Bijective f' := ⟨hf_inj, hf_surj⟩
  have h_card_eq : Nat.card conjs = Nat.card (G ⧸ M) :=
    (Nat.card_congr (Equiv.ofBijective f' hbij)).symm
  rw [← Nat.card_coe_set_eq, h_card_eq, ← Subgroup.index]

/-- **Hall conjugacy** (Coq `Hall_subJ` for the solvable maximal `M`): in a maximal subgroup `M`,
every `π`-subgroup `X ≤ M` is conjugate by an element of `M` into any Hall `π`-subgroup `K` of `M`.
This is the general-`π` form of `exists_conj_smul_le_isHall_kappa` (which specialises `π = κ(M)`);
the proof embeds `X` in a Hall `π`-subgroup of the solvable `↥M` and conjugates the two Hall
subgroups together (`exists_conj_eq_of_isHall_subgroupOf`). -/
theorem exists_conj_smul_le_of_isHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {π : Set ℕ} (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup π (K.subgroupOf M))
    {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Ch03.Subgroup.IsPiGroup π (X.subgroupOf M)) :
    ∃ w ∈ M, MulAut.conj w • X ≤ K := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨H, hH_hall, -, hX_le_H⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
      hXpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup π (HG.subgroupOf M) := by
    rwa [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M hKM
      hHG_hall hK
  have hXHG : X ≤ HG := by
    intro x hx
    rw [hHGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩, hX_le_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact ⟨w, hwM, (conj_smul_mono (MulAut.conj w) hXHG).trans hw.le⟩

/-- **Converse of `isPiElement_sigma_of_mem_Msigma`** (Coq `mem_Hall_pcore (Msigma_Hall maxM)`):
a `σ(M)`-element `x ∈ M` lies in `M_σ`.  The image of `x` in the quotient `M / M_σ` is a
`σ(M)`-element (a power of `x`), but `M_σ` is a Hall `σ(M)`-subgroup of `M` so `M / M_σ` is a
`σ(M)′`-group; hence the image is trivial and `x ∈ M_σ`. -/
theorem mem_Msigma_of_isPiElement_sigma_of_mem [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxM : x ∈ M)
    (hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) :
    x ∈ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set Ms : Subgroup ↥M := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M with hMs
  haveI hNorm : Ms.Normal := by rw [hMs, OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) Ms :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
  set xM : ↥M := ⟨x, hxM⟩ with hxMdef
  have hord : orderOf xM = orderOf x :=
    (orderOf_injective M.subtype M.subtype_injective xM).symm
  set q : ↥M ⧸ Ms := QuotientGroup.mk' Ms xM with hq
  have h1 : orderOf q ∣ orderOf xM := by
    rw [hq]; exact orderOf_map_dvd (QuotientGroup.mk' Ms) xM
  have hq1 : orderOf q = 1 := by
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := (orderOf q).exists_prime_and_dvd hne
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      hxpi p (Nat.mem_primeFactors.mpr
        ⟨hpprime, (hpdvd.trans h1).trans (dvd_of_eq hord), (orderOf_pos x).ne'⟩)
    have hpidx : p ∈ Ms.index.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpprime, by
        rw [Subgroup.index_eq_card]; exact hpdvd.trans (orderOf_dvd_natCard q),
        by rw [Subgroup.index_eq_card]; exact Nat.card_pos.ne'⟩
    exact hHall.index_no_pi p hpidx hpσ
  have hqone : q = 1 := orderOf_eq_one_iff.mp hq1
  have hxMmem : xM ∈ Ms := (QuotientGroup.eq_one_iff xM).mp hqone
  exact Subgroup.mem_subgroupOf.mp hxMmem

/-- **Coq `cent1_sub_uniq_sigma_mmax`** (BGsection14:1008, a supplement to Theorem 14.4): if
`𝓜_σ(x)` is a singleton, its unique element `M` contains `C_G(x)`.  Conjugation by any
`y ∈ C_G(x)` permutes `𝓜_σ(x)` (it fixes `x`), hence fixes the unique element `M`, so
`y ∈ N_G(M) = M`.  This is the linchpin of the `|𝓜_σ(x')| > 1` step in BG Lemma 14.6. -/
theorem centralizer_le_of_maximalSigma_ncard_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {x : G} {M : Subgroup G}
    (hcard : (maximalSigmaSubgroupsOfElement x).ncard = 1)
    (hM : M ∈ maximalSigmaSubgroupsOfElement x) :
    Subgroup.centralizer ({x} : Set G) ≤ M := by
  classical
  obtain ⟨N, hsingle⟩ := Set.ncard_eq_one.mp hcard
  have hmax : M ∈ maximalSubgroups G := hM.1
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hM.2
  intro y hy
  have hcom : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton x)
  -- `y` fixes `x` by conjugation.
  have hyx : MulAut.conj y • x = x := by
    rw [MulAut.smul_def, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]; exact hcom.symm
  -- `Mʸ ∈ 𝓜_σ(x)`: it is maximal and `x = y·x·y⁻¹ ∈ Mʸ_σ`.
  have hconjMem : (MulAut.conj y • M) ∈ maximalSigmaSubgroupsOfElement x := by
    refine ⟨mem_maximalSubgroups.mpr (isCoatom_conj_smul (mem_maximalSubgroups.mp hmax)), ?_⟩
    rw [Msigma_conj_smul, ← hyx]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj y) (OddOrder.BG.Ch3.S10.Msigma M) hxMσ
  -- both lie in the singleton `{N}`, so `Mʸ = M`.
  have heq : MulAut.conj y • M = M := by
    rw [hsingle, Set.mem_singleton_iff] at hconjMem hM; rw [hconjMem, ← hM]
  -- hence `y ∈ N_G(M) = M`.
  have hyN : y ∈ Subgroup.normalizer (M : Set G) :=
    OddOrder.BG.Ch1.S03f.mem_normalizer_of_map_conj_eq heq
  rwa [normalizer_eq_self_of_mem_maximalSubgroups hG hmax] at hyN

/-- **Honest content of Coq `s'g`** (the heart of BG Lemma 14.6,
`sigma_decomposition_dichotomy`): for `x ∈ M_σ^#` and a nonidentity `σ(M)′`-element `x'` of `M`
that centralizes `x`, the product `g = x · x'` falls into one of the two branches of the
σ-decomposition dichotomy:

* the **signalizer branch** — some `y` with `ℓ_σ(y) = 1` and `y⁻¹ g ∈ R(y)` (witnessed by
  `y = x'`, with `x'⁻¹ g = x ∈ R(x')`); or
* the **κ branch** — `ℓ_σ(x) = 1`, `M ∈ 𝓜_σ(x)`, `x' ∈ (C_M[x])^#`, and `x'` is a
  `κ(M)`-element.

This is the direct consumer of `sigma_diagnostic` (BG Cor 14.3 / `pi_of_cent_sigma`): the τ₂
branch lands in the signalizer disjunct (using `centralizer_le_of_maximalSigma_ncard_eq_one`
to force `|𝓜_σ(x')| > 1` and `exists_neighbor_eq_Rsub` to identify the neighbour `N` with `M`),
and the κ branch lands in the κ disjunct verbatim. -/
theorem signalizer_coset_or_kappa_of_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x x' : G}
    (hx : x ∈ sigmaSharp M) (hx'M : x' ∈ M) (hx'1 : x' ≠ 1)
    (hx'cent : x' ∈ Subgroup.centralizer ({x} : Set G))
    (hx'sigma : ∀ p ∈ piSet (Subgroup.closure {x'}), p ∉ OddOrder.BG.Ch3.S10.sigma M) :
    (∃ y, D.length y = 1 ∧ y⁻¹ * (x * x') ∈ Rsub hG D y)
    ∨ (D.length x = 1 ∧ M ∈ maximalSigmaSubgroupsOfElement x ∧
        x' ∈ sharpSubgroup (M ⊓ Subgroup.centralizer ({x} : Set G)) ∧
        OddOrder.GroupTheory.IsPiElement (kappa M) x') := by
  classical
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  -- `x` and `x'` commute.
  have hcomm : x * x' = x' * x := (Subgroup.mem_centralizer_iff.mp hx'cent) x (Set.mem_singleton x)
  rcases sigma_diagnostic hG D hM ⟨hxMσ, hx1⟩ hx'M hx'1 hx'cent hx'sigma with
    ⟨hκ, _⟩ | ⟨_, hlen', huniq⟩
  · -- **κ branch**.
    refine Or.inr ⟨?_, ⟨hM, hxMσ⟩, ?_, ?_⟩
    · exact length_one_of_isPiElement_sigma hG D hM hx1 (isPiElement_sigma_of_mem_Msigma hxMσ)
    · exact Set.mem_sdiff_singleton.mpr ⟨Subgroup.mem_inf.mpr ⟨hx'M, hx'cent⟩, hx'1⟩
    · intro p hp
      refine hκ p ?_
      change p ∈ (Nat.card ↥(Subgroup.closure ({x'} : Set G))).primeFactors
      rwa [show Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' from by
        rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]]
  · -- **signalizer branch** (τ₂ case): `y = x'`, `x'⁻¹ g = x ∈ R(x')`.
    refine Or.inl ⟨x', hlen', ?_⟩
    have hxx' : x'⁻¹ * (x * x') = x := by
      rw [hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hxx']
    -- `𝓜_σ(x')` is nonempty (from `ℓ_σ(x') = 1`).
    have hne' : (maximalSigmaSubgroupsOfElement x').Nonempty := ((D.length_one_iff x').mp hlen').2
    -- `|𝓜_σ(x')| > 1`.
    have hgt' : 1 < (maximalSigmaSubgroupsOfElement x').ncard := by
      rcases lt_or_ge 1 (maximalSigmaSubgroupsOfElement x').ncard with h | h
      · exact h
      · exfalso
        have hcard1 : (maximalSigmaSubgroupsOfElement x').ncard = 1 :=
          le_antisymm h ((Set.ncard_pos (Set.toFinite _)).mpr hne')
        obtain ⟨N₀, hN₀⟩ := hne'
        have hCx'N₀ : Subgroup.centralizer ({x'} : Set G) ≤ N₀ :=
          centralizer_le_of_maximalSigma_ncard_eq_one hG hcard1 hN₀
        have hN₀M : N₀ = M := by
          have hmem : N₀ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) :=
            ⟨mem_maximalSubgroups.mp hN₀.1, hCx'N₀⟩
          rw [huniq, Set.mem_singleton_iff] at hmem; exact hmem
        have hx'σM : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x' :=
          isPiElement_sigma_of_mem_Msigma (hN₀M ▸ hN₀.2)
        obtain ⟨p, hp⟩ : (orderOf x').primeFactors.Nonempty :=
          Nat.nonempty_primeFactors.mpr (by
            have h1 : orderOf x' ≠ 1 := by simpa [orderOf_eq_one_iff] using hx'1
            have h0 : 0 < orderOf x' := orderOf_pos x'
            omega)
        refine hx'sigma p ?_ (hx'σM p hp)
        change p ∈ (Nat.card ↥(Subgroup.closure ({x'} : Set G))).primeFactors
        rwa [show Nat.card ↥(Subgroup.closure ({x'} : Set G)) = orderOf x' from by
          rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]]
    -- the neighbour `N = N(x')` of Theorem 14.4, with `R(x') = N_σ ∩ C_G(x')`.
    obtain ⟨N, hNmax, hCx'N, hRsub_eq, _, _⟩ := exists_neighbor_eq_Rsub hG D hlen' hgt'
    have hNM : N = M := by
      have hmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) :=
        ⟨mem_maximalSubgroups.mp hNmax, hCx'N⟩
      rw [huniq, Set.mem_singleton_iff] at hmem; exact hmem
    rw [hRsub_eq, hNM]
    refine Subgroup.mem_inf.mpr ⟨hxMσ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz; rw [Set.mem_singleton_iff.mp hz, ← hcomm]

/-- **Coq `s'g`, the `g ∈ M` corollary** — the σ-decomposition dichotomy for an element contained
in a maximal subgroup.  If `g ∈ M` (maximal) and the `σ(M)`-part of `g` is nontrivial, then `g`
lands in the signalizer branch or the κ branch.  Combines `mem_Msigma_of_isPiElement_sigma_of_mem`
(to see the `σ(M)`-part `x ∈ M_σ^#`) with `signalizer_coset_or_kappa_of_sigmaSharp` (applied to `x`
and the `σ(M)′`-part `x' = x⁻¹g`).  This is the form consumed by the full BG Lemma 14.6 assembly. -/
theorem branchA_or_branchB_of_mem_maximal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∈ M)
    (hne : sigmaPart M g ≠ 1) :
    (∃ y, D.length y = 1 ∧ y⁻¹ * g ∈ Rsub hG D y)
    ∨ (∃ y, D.length y = 1 ∧ ∃ N, N ∈ maximalSigmaSubgroupsOfElement y ∧
        y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)) ∧
        OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) := by
  classical
  simp only [sigmaPart] at hne
  obtain ⟨b, hbmul, hbcomm, hxπ, hbπ, hxz, hbz⟩ := piPart_spec (OddOrder.BG.Ch3.S10.sigma M) g
  set x := piPart (OddOrder.BG.Ch3.S10.sigma M) g with hxdef
  have hx1 : x ≠ 1 := hne
  have hxM : x ∈ M := Subgroup.zpowers_le.mpr hg hxz
  have hbM : b ∈ M := Subgroup.zpowers_le.mpr hg hbz
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    mem_Msigma_of_isPiElement_sigma_of_mem hG hM hxM hxπ
  have hxsharp : x ∈ sigmaSharp M := by
    rw [sigmaSharp, sharpSubgroup]; exact Set.mem_sdiff_singleton.mpr ⟨hxMσ, hx1⟩
  have hxg : x⁻¹ * g = b := by rw [← hbmul, ← mul_assoc, inv_mul_cancel, one_mul]
  have hlen : D.length x = 1 := length_one_of_isPiElement_sigma hG D hM hx1 hxπ
  by_cases hb1 : b = 1
  · refine Or.inl ⟨x, hlen, ?_⟩
    rw [hxg, hb1]; exact Subgroup.one_mem _
  · have hbcent : b ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro z hz
      rw [Set.mem_singleton_iff.mp hz]; exact hbcomm
    have hbσ : ∀ p ∈ piSet (Subgroup.closure {b}), p ∉ OddOrder.BG.Ch3.S10.sigma M := by
      intro p hp
      refine hbπ p ?_
      rwa [show orderOf b = Nat.card ↥(Subgroup.closure ({b} : Set G)) from by
        rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]]
    rcases signalizer_coset_or_kappa_of_sigmaSharp hG D hM hxsharp hbM hb1 hbcent hbσ with hA | hB
    · obtain ⟨y, hyl, hyr⟩ := hA
      exact Or.inl ⟨y, hyl, by rwa [hbmul] at hyr⟩
    · obtain ⟨hxl, hMmem, hbsharp, hbκ⟩ := hB
      exact Or.inr ⟨x, hxl, M, hMmem, by rw [hxg]; exact hbsharp, by rw [hxg]; exact hbκ⟩

/-- **BG Lemma 14.6** (`sigma_decomposition_dichotomy`, Coq `BGsection14`:1189): every `g ≠ 1`
satisfies (at least) one of the two branches of the σ-decomposition dichotomy: the **signalizer
branch** (`∃ y, ℓ_σ(y) = 1 ∧ y⁻¹g ∈ R(y)`) or the **κ branch** (`∃ y, ℓ_σ(y) = 1 ∧ ∃ N ∈ 𝓜_σ(y),
y⁻¹g ∈ (C_N[y])^#` with `y⁻¹g` a `κ(N)`-element).

Proof (Coq's second half): assume both branches fail.  Then `branchA_or_branchB_of_mem_maximal`
gives **`s'g`**: every `g ∈ M` (maximal) has trivial `σ(M)`-part.  Pick `x = (g)_{σ(M₀)} ≠ 1` from
the nonempty σ-decomposition; conjugate `M₀` so that `x ∈ M_σ` (preserving `σ(M) = σ(M₀)`, hence
`x = (g)_{σ(M)}`).  Then `g ∉ M` (else `s'g` kills `x`), so `|𝓜_σ(x)| > 1`
(`centralizer_le_of_maximalSigma_ncard_eq_one`).  The neighbour `N = N(x)` of Theorem 14.4 has
`C_G(x) ≤ N` and `M ∩ N` a Hall `σ(N)′`-subgroup of `N` (complement of `N_σ`); since `g` is a
`σ(N)′`-element (`s'g` for `N`), `⟨g⟩` conjugates into `M ∩ N ⊆ M` (`exists_conj_smul_le_of_isHall`),
so `(g^w)_{σ(M)} = (x)^w = 1` by `s'g`, forcing `x = 1` — a contradiction. -/
theorem sigma_decomposition_dichotomy [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {g : G} (hg : g ≠ 1) :
    (∃ y, D.length y = 1 ∧ y⁻¹ * g ∈ Rsub hG D y)
    ∨ (∃ y, D.length y = 1 ∧ ∃ N, N ∈ maximalSigmaSubgroupsOfElement y ∧
        y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)) ∧
        OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) := by
  classical
  by_contra hcon
  have hnA : ¬ (∃ y, D.length y = 1 ∧ y⁻¹ * g ∈ Rsub hG D y) := fun h => hcon (Or.inl h)
  have hnB : ¬ (∃ y, D.length y = 1 ∧ ∃ N, N ∈ maximalSigmaSubgroupsOfElement y ∧
      y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)) ∧
      OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) := fun h => hcon (Or.inr h)
  -- **`s'g`**: `g ∈ M` (maximal) ⟹ `σ(M)`-part of `g` is trivial.
  have hsg : ∀ M, M ∈ maximalSubgroups G → g ∈ M → sigmaPart M g = 1 := by
    intro M hM hgM
    by_contra hne
    rcases branchA_or_branchB_of_mem_maximal hG D hM hgM hne with hA | hB
    · exact hnA hA
    · exact hnB hB
  -- σ-decomposition is nonempty; pick `x = (g)_{σ(M₀)} ≠ 1`.
  have hlen0 : sigmaLength g ≠ 0 := fun h => hg ((sigmaLength_eq_zero_iff hG g).mp h)
  obtain ⟨x, hxmem⟩ : (sigmaDecomposition g).Nonempty := by
    rw [sigmaLength] at hlen0; exact Set.nonempty_of_ncard_ne_zero hlen0
  rw [sigmaDecomposition, Set.mem_sdiff, Set.mem_singleton_iff] at hxmem
  obtain ⟨⟨M₀, hM₀, hxeq⟩, hx1⟩ := hxmem
  have hxπ₀ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M₀) x :=
    hxeq ▸ isPiElement_piPart (OddOrder.BG.Ch3.S10.sigma M₀) g
  have hxz : x ∈ Subgroup.zpowers g := hxeq ▸ piPart_mem_zpowers (OddOrder.BG.Ch3.S10.sigma M₀) g
  have hxlen : D.length x = 1 := length_one_of_isPiElement_sigma hG D hM₀ hx1 hxπ₀
  -- **WLOG `x ∈ M_σ`**: conjugate `M₀` into a maximal `M` containing `x` in its `σ`-core.
  have hclosne : Subgroup.closure ({x} : Set G) ≠ ⊥ := fun h =>
    hx1 (Subgroup.mem_bot.mp (h ▸ Subgroup.subset_closure (Set.mem_singleton x)))
  have hclt : Subgroup.closure ({x} : Set G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hG.notSolvable (isSolvable_of_comm fun a b => ?_))
    have hmem : ∀ y : G, y ∈ Subgroup.zpowers x := fun y => by
      rw [Subgroup.zpowers_eq_closure, htop]; exact Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := hmem a; obtain ⟨n, rfl⟩ := hmem b
    rw [← zpow_add, ← zpow_add, Int.add_comm]
  have hxpisub : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M₀)
      (Subgroup.closure ({x} : Set G)) := fun p hp =>
    hxπ₀ p (by rwa [← Subgroup.zpowers_eq_closure, Nat.card_zpowers] at hp)
  obtain ⟨c, hc⟩ := sigma_subgroup_conj_into_Msigma_general hG hM₀ hclosne hclt hxpisub
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM₀ hN hnc)
  set M := MulAut.conj c⁻¹ • M₀ with hMdef
  have hMmax : M ∈ maximalSubgroups G :=
    mem_maximalSubgroups_of_isConjugateSubgroup hM₀ ⟨c⁻¹, rfl⟩
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [hMdef, Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcx : MulAut.conj c • x ∈ OddOrder.BG.Ch3.S10.Msigma M₀ :=
      hc (Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) _
        (Subgroup.subset_closure (Set.mem_singleton x)))
    rwa [show (MulAut.conj c⁻¹)⁻¹ • x = MulAut.conj c • x from by rw [← map_inv, inv_inv]]
  have hσM : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma M₀ := by
    rw [hMdef, sigma_conj_smul_eq]
  have hxsig : sigmaPart M g = x := by rw [sigmaPart, hσM, ← sigmaPart, ← hxeq]
  -- `g ∉ M`, `g ∈ C_G(x)`, `M ∈ 𝓜_σ(x)`.
  have hnotMg : g ∉ M := fun hgM => hx1 (hxsig ▸ hsg M hMmax hgM)
  have hcxg : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    obtain ⟨k, hk⟩ := hxz; rw [← hk]; exact Commute.zpow_left (Commute.refl g) k
  have hMmemx : M ∈ maximalSigmaSubgroupsOfElement x := ⟨hMmax, hxMσ⟩
  -- `|𝓜_σ(x)| > 1` (else `C_G(x) ≤ M`, so `g ∈ M`).
  have hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra hle
    push Not at hle
    have hcard1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 :=
      le_antisymm hle ((Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hMmemx⟩)
    exact hnotMg ((centralizer_le_of_maximalSigma_ncard_eq_one hG hcard1 hMmemx) hcxg)
  -- Neighbour `N = N(x)`: `C_G(x) ≤ N`, and `M ∩ N` complements `N_σ` in `N`.
  obtain ⟨N, hNmax, hCxN, -, -, hcompl⟩ := exists_neighbor_eq_Rsub hG D hxlen hgt
  have hcomplM := hcompl M hMmemx
  have hgN : g ∈ N := hCxN hcxg
  have hsigNg : sigmaPart N g = 1 := hsg N hNmax hgN
  have hsN'g : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ g :=
    isPiElement_compl_of_piPart_eq_one hsigNg
  -- `M ∩ N` is a Hall `σ(N)′`-subgroup of `N`.
  have hMsHall := OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hNmax
  have hMNhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ ((M ⊓ N).subgroupOf N) := by
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [(hcomplM.symm.index_eq_card).symm] at hp
      exact hMsHall.index_no_pi p hp
    · rw [hcomplM.index_eq_card] at hp
      rw [Set.mem_compl_iff, not_not]
      exact hMsHall.primeFactors_card_subset p hp
  -- `⟨g⟩` is a `σ(N)′`-subgroup of `N`.
  have hgN_le : Subgroup.zpowers g ≤ N := Subgroup.zpowers_le.mpr hgN
  have hgpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ
      ((Subgroup.zpowers g).subgroupOf N) := by
    intro p hp
    refine hsN'g p ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hgN_le).toEquiv, Nat.card_zpowers] at hp
  -- Conjugate `⟨g⟩` into `M ∩ N`, so a conjugate of `g` lies in `M`.
  obtain ⟨w, _, hwle⟩ :=
    exists_conj_smul_le_of_isHall hG hNmax (inf_le_right) hMNhall hgN_le hgpi
  have hwg : MulAut.conj w • g ∈ M := by
    have hmem : MulAut.conj w • g ∈ M ⊓ N :=
      hwle (Subgroup.smul_mem_pointwise_smul g (MulAut.conj w) _ (Subgroup.mem_zpowers g))
    exact (Subgroup.mem_inf.mp hmem).1
  -- `g ∈ Mʷ⁻¹` (a maximal conjugate of `M`); `s'g` there gives `(g)_{σ(M)} = x = 1`.
  have hM' : MulAut.conj w⁻¹ • M ∈ maximalSubgroups G :=
    mem_maximalSubgroups_of_isConjugateSubgroup hMmax ⟨w⁻¹, rfl⟩
  have hgM' : g ∈ MulAut.conj w⁻¹ • M := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show (MulAut.conj w⁻¹)⁻¹ • g = MulAut.conj w • g from by rw [← map_inv, inv_inv]]
    exact hwg
  have hfinal : sigmaPart (MulAut.conj w⁻¹ • M) g = 1 := hsg _ hM' hgM'
  rw [sigmaPart, sigma_conj_smul_eq, ← sigmaPart, hxsig] at hfinal
  exact hx1 hfinal

/-- **BG Corollary 14.9, the type-I cover (faithful form)**: when every maximal subgroup is of
type `F` (`κ(M) = ∅`, so there is no exceptional `κ` branch), every nonidentity `g` lies in some
`𝒞_G(M̃)`.  Immediate from `sigma_decomposition_dichotomy`: the signalizer branch gives
`y` with `ℓ_σ(y) = 1` and `y⁻¹g ∈ R(y)`, so `g ∈ M̃(M)` (`mem_Mtilde_of_mem_coset`, with `M` the
maximal carrying `y ∈ M_σ^#`); the `κ` branch is impossible because a nonidentity `κ(N)`-element
would force `κ(N) ≠ ∅`, contradicting `IsTypeF N`.

**Faithfulness note:** without the all-type-`F` hypothesis the statement is *false* — `κ`-branch
elements lie in the exceptional `𝒞_G(Ẑ)` piece and in no `𝒞_G(M̃)` (the dichotomy is an XOR).  The
cover uses the canonical `genuineSigmaDecomposition`, matching `bgTheoremE_cover_data`'s `cover`. -/
theorem exists_mem_conjClassSet_Mtilde_of_ne_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M ∈ maximalSubgroups G, IsTypeF M) {g : G} (hg : g ≠ 1) :
    ∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · -- **Signalizer branch**: `y⁻¹g ∈ R(y)` puts `g` in `M̃(M)` for the maximal `M ∋ y` in `M_σ`.
    obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · -- **κ branch**: impossible under all-type-`F` (`κ(N) = ∅`).
    exfalso
    have hN1 : y⁻¹ * g ≠ 1 := (Set.mem_sdiff_singleton.mp hsharp).2
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    have hpκ : p ∈ kappa N := hκ p hp
    rw [hall N hNmem.1] at hpκ
    exact (Set.mem_empty_iff_false p).mp hpκ

/-- `|L_σ^#| = |M_σ^#|` whenever `L` is a conjugate of `M`: conjugation is an order-preserving
bijection, so `|L_σ| = |M_σ|` and removing the (fixed) identity preserves the count. -/
theorem sharpSubgroup_Msigma_ncard_of_isConjugate [Finite G] {M L : Subgroup G}
    (h : IsConjugateSubgroup M L) :
    (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma L)).ncard
      = (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard := by
  have key : ∀ H : Subgroup G, (sharpSubgroup H).ncard = Nat.card ↥H - 1 := fun H => by
    have hc : Nat.card ↥H = (H : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
    rw [sharpSubgroup, Set.ncard_sdiff (Set.singleton_subset_iff.mpr H.one_mem),
      Set.ncard_singleton, hc]
  rw [key, key]
  congr 1
  obtain ⟨a, rfl⟩ := h
  rw [Msigma_conj_smul, OddOrder.BG.Ch3.S10.conjSmul_eq_map]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj a).injective).toEquiv).symm

/-- **All members of `𝓜_σ(x)` are conjugate** (BG Theorem 14.4 sharp transitivity): `R(x)` acts
transitively on `𝓜_σ(x)`, so any two `σ`-maximals of a `σ`-length-one element are conjugate.  In
the single-maximal case `𝓜_σ(x)` is a singleton, so the two coincide. -/
theorem isConjugateSubgroup_of_mem_maximalSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {x : G}
    (hlen : D.length x = 1) {L L' : Subgroup G}
    (hL : L ∈ maximalSigmaSubgroupsOfElement x) (hL' : L' ∈ maximalSigmaSubgroupsOfElement x) :
    IsConjugateSubgroup L L' := by
  classical
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
    obtain ⟨r, hr, -⟩ := (spec.2.2.2.2.2.2 L hL).2.2.2 L' hL'
    exact ⟨r, hr.2⟩
  · have hne : (maximalSigmaSubgroupsOfElement x).Nonempty := ((D.length_one_iff x).mp hlen).2
    have hfin : (maximalSigmaSubgroupsOfElement x).Finite := Set.toFinite _
    have h1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 := by
      have hpos : 0 < (maximalSigmaSubgroupsOfElement x).ncard := by
        rw [Set.ncard_pos hfin]; exact hne
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    rw [ha, Set.mem_singleton_iff] at hL hL'
    rw [hL, hL']

/-- **Sharp transitivity, `C_G(x)`-witness form** (BG Theorem 14.4, strengthening
`isConjugateSubgroup_of_mem_maximalSigma`): for a `σ`-length-one `x`, `R(x) = N_σ ∩ C_G(x)` acts
transitively on `𝓜_σ(x)`, so any two `σ`-maximals `L, L'` of `x` satisfy `L' = L^c` for some
`c ∈ C_G(x)` — not merely some `c ∈ G`.  This `C_G(x)`-conjugacy is the form BG Corollary 15.3(b)
consumes (after `N_G(M) = M` it forces the conjugator into `M`). -/
theorem exists_conj_centralizer_of_mem_maximalSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {x : G}
    (hlen : D.length x = 1) {L L' : Subgroup G}
    (hL : L ∈ maximalSigmaSubgroupsOfElement x) (hL' : L' ∈ maximalSigmaSubgroupsOfElement x) :
    ∃ c ∈ Subgroup.centralizer ({x} : Set G), MulAut.conj c • L = L' := by
  classical
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
    obtain ⟨r, hr, -⟩ := (spec.2.2.2.2.2.2 L hL).2.2.2 L' hL'
    exact ⟨r, (Subgroup.mem_inf.mp hr.1).2, hr.2⟩
  · have hne : (maximalSigmaSubgroupsOfElement x).Nonempty := ((D.length_one_iff x).mp hlen).2
    have h1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 := by
      have hpos : 0 < (maximalSigmaSubgroupsOfElement x).ncard := by
        rw [Set.ncard_pos (Set.toFinite _)]; exact hne
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    rw [ha, Set.mem_singleton_iff] at hL hL'
    exact ⟨1, Subgroup.one_mem _, by rw [hL, hL', map_one, one_smul]⟩

/-- **BG Corollary 15.3(b), `hconj` input** (the `§14.4` half): for a maximal `M` and
`H ≤ M_σ`, any two elements `x, y ∈ H` that are conjugate in `G` are already conjugate by an
element of `M`.  (`N_M(H)`-control is then obtained from this via the Frattini argument in the
`H ⋬ M` case.)

Proof.  If `x = 1` then `y = 1` and `m = 1` works.  Otherwise `x ∈ M_σ` has `σ`-length one, with
`M ∈ 𝓜_σ(x)` and `M^{g⁻¹} ∈ 𝓜_σ(x)` (as `x = g⁻¹yg ∈ (M_σ)^{g⁻¹}`).  Theorem 14.4's sharp
transitivity (`exists_conj_centralizer_of_mem_maximalSigma`) yields `c ∈ C_G(x)` with
`M^{cg⁻¹} = M`, so `cg⁻¹ ∈ N_G(M) = M`; then `m = (cg⁻¹)⁻¹ = gc⁻¹ ∈ M` and
`m x m⁻¹ = g(c⁻¹xc)g⁻¹ = gxg⁻¹ = y`. -/
theorem mf_hall_conj_realized_in_M [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hHMσ : H ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    ∀ x ∈ H, ∀ y ∈ H, ∀ g : G, y = g * x * g⁻¹ → ∃ m ∈ M, y = m * x * m⁻¹ := by
  classical
  intro x hx y hy g hyg
  by_cases hx1 : x = 1
  · exact ⟨1, M.one_mem, by rw [hyg, hx1]; group⟩
  · have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hHMσ hx
    have hMmem : M ∈ maximalSigmaSubgroupsOfElement x := ⟨hM, hxMσ⟩
    have hgM_max : MulAut.conj g⁻¹ • M ∈ maximalSubgroups G :=
      mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g⁻¹, rfl⟩
    have hxgMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g⁻¹ • M) := by
      rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have heq : (MulAut.conj g⁻¹)⁻¹ • x = y := by
        rw [map_inv, inv_inv, MulAut.smul_def, MulAut.conj_apply]; exact hyg.symm
      rw [heq]; exact hHMσ hy
    have hgMmem : MulAut.conj g⁻¹ • M ∈ maximalSigmaSubgroupsOfElement x := ⟨hgM_max, hxgMσ⟩
    have hlen : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨M, hMmem⟩⟩
    obtain ⟨c, hcC, hcconj⟩ :=
      exists_conj_centralizer_of_mem_maximalSigma hG D hlen hgMmem hMmem
    have hcg : MulAut.conj (c * g⁻¹) • M = M := by rw [map_mul, mul_smul]; exact hcconj
    have hcgM : c * g⁻¹ ∈ M := by
      rw [← normalizer_eq_self_of_mem_maximalSubgroups hG hM]
      exact mem_normalizer_of_conj_smul_eq_self hcg
    have hcomm : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hcC) x (Set.mem_singleton x)
    have hcx' : c⁻¹ * x * c = x := by rw [mul_assoc, hcomm, inv_mul_cancel_left]
    refine ⟨(c * g⁻¹)⁻¹, M.inv_mem hcgM, ?_⟩
    calc y = g * x * g⁻¹ := hyg
      _ = g * (c⁻¹ * x * c) * g⁻¹ := by rw [hcx']
      _ = (c * g⁻¹)⁻¹ * x * ((c * g⁻¹)⁻¹)⁻¹ := by group

/-- A conjugacy-saturation `𝒞_G(M_σ^#)` element is nonidentity (it is conjugate to some
`t ∈ M_σ^#`, and conjugation fixes the identity). -/
theorem ne_one_of_mem_sigmaConjugacySaturation {M : Subgroup G} {x : G}
    (hx : x ∈ sigmaConjugacySaturation M) : x ≠ 1 := by
  rw [sigmaConjugacySaturation, sigmaSharp, mem_conjClassSet] at hx
  obtain ⟨t, ht, g, hgt⟩ := hx
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at ht
  rw [← hgt]; intro h
  have e : g * t * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
  exact ht.2 (mul_left_cancel (mul_right_cancel e))

/-- Every `x ∈ 𝒞_G(M_σ^#)` is a `σ`-length-one element with a conjugate of `M` among its
`σ`-maximals (`x = t^a` with `t ∈ M_σ^#` puts `x ∈ (M^a)_σ`).  This routes `Rsub_ncard_eq`
(needs `ℓ_σ(x) = 1`) and the fibre identification of Lemma 14.5(c). -/
theorem length_one_of_mem_sigmaConjugacySaturation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ sigmaConjugacySaturation M) :
    D.length x = 1 ∧ ∃ a : G, MulAut.conj a • M ∈ maximalSigmaSubgroupsOfElement x := by
  classical
  rw [sigmaConjugacySaturation, sigmaSharp, mem_conjClassSet] at hx
  obtain ⟨t, ht, g, hgt⟩ := hx
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at ht
  obtain ⟨htM, ht1⟩ := ht
  have hx1 : x ≠ 1 := by
    rw [← hgt]; intro h
    have e : g * t * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    exact ht1 (mul_left_cancel (mul_right_cancel e))
  have hmem : MulAut.conj g • M ∈ maximalSigmaSubgroupsOfElement x := by
    refine ⟨mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g, rfl⟩, ?_⟩
    rw [Msigma_conj_smul, ← hgt, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcalc : (MulAut.conj g)⁻¹ • (g * t * g⁻¹) = t := by
      rw [← map_inv (MulAut.conj) g, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
    rw [hcalc]; exact htM
  exact ⟨(D.length_one_iff x).mpr ⟨hx1, ⟨MulAut.conj g • M, hmem⟩⟩, g, hmem⟩

/-- **Fibre over `x`** (BG 14.5(c) double count): for `x ∈ 𝒞_G(M_σ^#)`, the `σ`-maximals `𝓜_σ(x)`
are exactly the conjugates `L` of `M` with `x ∈ L_σ`.  (All of `𝓜_σ(x)` are conjugate by sharp
transitivity, and one of them is a conjugate of `M`.) -/
theorem maximalSigma_eq_conj_of_mem_saturation [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ sigmaConjugacySaturation M) :
    maximalSigmaSubgroupsOfElement x
      = {L | IsConjugateSubgroup M L ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma L} := by
  obtain ⟨hlen, a, hL0⟩ := length_one_of_mem_sigmaConjugacySaturation hG D hM hx
  ext L
  refine ⟨fun hL => ⟨IsConjugateSubgroup.trans ⟨a, rfl⟩
      (isConjugateSubgroup_of_mem_maximalSigma hG D hlen hL0 hL), hL.2⟩,
    fun hLc => ⟨mem_maximalSubgroups_of_isConjugateSubgroup hM hLc.1, hLc.2⟩⟩

/-- **Fibre over `L`** (BG 14.5(c) double count): for `L` conjugate to `M`, the saturated
elements lying in `L_σ` are exactly `L_σ^#`. -/
theorem saturation_inter_Msigma_eq_sharp [Finite G] {M L : Subgroup G}
    (hconj : IsConjugateSubgroup M L) :
    {x | x ∈ sigmaConjugacySaturation M ∧ x ∈ OddOrder.BG.Ch3.S10.Msigma L}
      = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma L) := by
  ext x
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, Set.mem_setOf_eq]
  refine ⟨fun hx => ⟨hx.2, ne_one_of_mem_sigmaConjugacySaturation hx.1⟩, fun hx => ⟨?_, hx.1⟩⟩
  obtain ⟨a, rfl⟩ := hconj
  rw [sigmaConjugacySaturation, sigmaSharp, mem_conjClassSet]
  rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  set t := (MulAut.conj a)⁻¹ • x with htdef
  have hax : a * t * a⁻¹ = x := by
    rw [htdef, ← map_inv (MulAut.conj) a, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
  refine ⟨t, ?_, a, hax⟩
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
  exact ⟨hx.1, fun ht1 => hx.2 (by rw [← hax, ht1]; group)⟩

/-- **BG Lemma 14.5(c), the double count** (mmd L3933-3940): summing `|R(x)|` over the conjugacy
saturation `𝒞_G(M_σ^#)` gives `|M_σ^#|·[G:M]`.  Counts pairs `(x, L)` with `L` a conjugate of `M`
and `x ∈ L_σ^#` two ways — by `x` (each contributes `|𝓜_σ(x)| = |R(x)|`, sharp transitivity) and
by `L` (each of the `[G:M]` conjugates contributes `|L_σ^#| = |M_σ^#|`). -/
theorem sigmaSaturation_Rsub_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∑ x ∈ (Set.toFinite (sigmaConjugacySaturation M)).toFinset, Nat.card ↥(Rsub hG D x)
      = (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard * M.index := by
  classical
  set Sfin := (Set.toFinite (sigmaConjugacySaturation M)).toFinset with hSf
  set Conjfin := (Set.toFinite {L : Subgroup G | IsConjugateSubgroup M L}).toFinset with hCf
  -- Step 1: rewrite each `|R(x)|` as the `x`-fibre count over conjugates of `M`.
  have step1 : ∀ x ∈ Sfin, Nat.card ↥(Rsub hG D x)
      = ∑ L ∈ Conjfin, (if x ∈ OddOrder.BG.Ch3.S10.Msigma L then 1 else 0) := by
    intro x hxfin
    have hxS : x ∈ sigmaConjugacySaturation M := by
      rw [hSf, Set.Finite.mem_toFinset] at hxfin; exact hxfin
    have hlen := (length_one_of_mem_sigmaConjugacySaturation hG D hM hxS).1
    have hcoe : (↑(Conjfin.filter (fun L => x ∈ OddOrder.BG.Ch3.S10.Msigma L)) : Set (Subgroup G))
        = maximalSigmaSubgroupsOfElement x := by
      rw [maximalSigma_eq_conj_of_mem_saturation hG D hM hxS]
      ext L
      simp only [Finset.mem_coe, Finset.mem_filter, hCf, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [Rsub_ncard_eq hG D hlen, ← hcoe, Set.ncard_coe_finset, Finset.card_filter]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  -- Step 3: each `L`-fibre is `|L_σ^#| = |M_σ^#|`, over the `[G:M]` conjugates of `M`.
  have step3 : ∀ L ∈ Conjfin,
      (∑ x ∈ Sfin, (if x ∈ OddOrder.BG.Ch3.S10.Msigma L then 1 else 0))
      = (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard := by
    intro L hLfin
    have hLconj : IsConjugateSubgroup M L := by
      rw [hCf, Set.Finite.mem_toFinset] at hLfin; exact hLfin
    have hcoe : (↑(Sfin.filter (fun x => x ∈ OddOrder.BG.Ch3.S10.Msigma L)) : Set G)
        = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma L) := by
      rw [← saturation_inter_Msigma_eq_sharp hLconj]
      ext y
      simp only [Finset.mem_coe, Finset.mem_filter, hSf, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    rw [← Finset.card_filter, ← Set.ncard_coe_finset, hcoe,
      sharpSubgroup_Msigma_ncard_of_isConjugate hLconj]
  rw [Finset.sum_congr rfl step3, Finset.sum_const, smul_eq_mul]
  have hConjcard : Conjfin.card = M.index := by
    rw [hCf, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    have hrange : {L : Subgroup G | IsConjugateSubgroup M L}
        = Set.range (fun g : G => MulAut.conj g • M) := rfl
    rw [hrange, ncard_conjugates_eq_index_of_normalizer_eq_self
      (normalizer_eq_self_of_mem_maximalSubgroups hG hM)]
  rw [hConjcard]
  exact Nat.mul_comm _ _

/-! #### Part B of Lemma 14.5(c): the cover `𝒞_G(M̃) = ⊔ₓ x R(x)` via `R`-equivariance -/

/-- The chosen neighbour `N(x)` of Theorem 14.4 (multi-maximal case), packaged with the
**singleton characterisation** `𝓜(C_G(x)) = {N(x)}` (BG mmd L3906).  The singleton clause is
Corollary 14.3's `maximalContaining_centralizer_eq_singleton_of_tau2_element` applied to the
`∃!`-spec data; it pins `N(x)` as the *unique* maximal subgroup containing `C_G(x)`, which is
exactly what makes `R(x)` conjugation-equivariant (`Rsub_conj`). -/
theorem exists_neighbor_Rsub_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hlen : D.length x = 1)
    (hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ Subgroup.centralizer ({x} : Set G) ≤ N ∧
      Rsub hG D x = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} := by
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  set N := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose with hNdef
  have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
  have hxN : x ∈ N := spec.2.1 (Subgroup.mem_centralizer_iff.mpr
    (fun a ha => by rw [Set.mem_singleton_iff.mp ha]))
  exact ⟨N, spec.1, spec.2.1, Rsub_eq_inf hG D hx hlen hgt,
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG spec.1 hxN hx
      spec.2.2.2.2.1 spec.2.2.1⟩

/-- **`𝓜_σ(x)` is conjugation-equivariant**: `𝓜_σ(gxg⁻¹) = (conj g) • 𝓜_σ(x)` (as the image
under `L ↦ Lᵍ`).  Conjugation by `g` is an order-isomorphism of subgroups carrying `M_σ` to
`(Mᵍ)_σ` (`Msigma_conj_smul`), so it bijects the `σ`-maximals of `x` with those of `gxg⁻¹`. -/
private theorem maximalSigmaSubgroupsOfElement_conj [Finite G] (g x : G) :
    maximalSigmaSubgroupsOfElement (g * x * g⁻¹)
      = (fun L : Subgroup G => MulAut.conj g • L) '' maximalSigmaSubgroupsOfElement x := by
  have key : ∀ L : Subgroup G, x ∈ OddOrder.BG.Ch3.S10.Msigma L
      ↔ g * x * g⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • L) := by
    intro L
    rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hcalc : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
      rw [← map_inv (MulAut.conj) g, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
    rw [hcalc]
  ext L
  constructor
  · rintro ⟨hLmax, hxL⟩
    have hL₀L : MulAut.conj g • (MulAut.conj g⁻¹ • L) = L := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    exact ⟨MulAut.conj g⁻¹ • L,
      ⟨mem_maximalSubgroups_of_isConjugateSubgroup hLmax ⟨g⁻¹, rfl⟩,
        by rw [key (MulAut.conj g⁻¹ • L), hL₀L]; exact hxL⟩, hL₀L⟩
  · rintro ⟨L₀, ⟨hL₀max, hxL₀⟩, rfl⟩
    exact ⟨mem_maximalSubgroups_of_isConjugateSubgroup hL₀max ⟨g, rfl⟩, (key L₀).mp hxL₀⟩

/-- **`R(x)` is conjugation-equivariant**: `R(gxg⁻¹) = (conj g) • R(x)` (BG mmd L3908, the
identity behind the cover `𝒞_G(M̃) = ⋃ₓ x R(x)`).  The `if`-condition of `R` is conjugation
invariant (`𝓜_σ` equivariance), and in the multi-maximal case `R(x) = N_σ ∩ C_G(x)` with `N(x)`
the *unique* maximal containing `C_G(x)`; since `N(x)ᵍ` is the unique maximal containing
`C_G(gxg⁻¹)`, it equals `N(gxg⁻¹)`, and the intersection conjugates accordingly. -/
theorem Rsub_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (g x : G) :
    Rsub hG D (g * x * g⁻¹) = MulAut.conj g • Rsub hG D x := by
  classical
  have hne1 : g * x * g⁻¹ ≠ 1 ↔ x ≠ 1 := by
    rw [ne_eq, ne_eq, mul_inv_eq_one, mul_eq_left]
  have himg : maximalSigmaSubgroupsOfElement (g * x * g⁻¹)
      = (fun L : Subgroup G => MulAut.conj g • L) '' maximalSigmaSubgroupsOfElement x :=
    maximalSigmaSubgroupsOfElement_conj g x
  have hinj : Function.Injective (fun L : Subgroup G => MulAut.conj g • L) :=
    fun a b h => by simpa using congrArg (fun L => (MulAut.conj g)⁻¹ • L) h
  have hncard : (maximalSigmaSubgroupsOfElement (g * x * g⁻¹)).ncard
      = (maximalSigmaSubgroupsOfElement x).ncard := by
    rw [himg, Set.ncard_image_of_injective _ hinj]
  have hne_iff : (maximalSigmaSubgroupsOfElement (g * x * g⁻¹)).Nonempty
      ↔ (maximalSigmaSubgroupsOfElement x).Nonempty := by rw [himg, Set.image_nonempty]
  have hcond_iff : (g * x * g⁻¹ ≠ 1 ∧ D.length (g * x * g⁻¹) = 1
        ∧ 1 < (maximalSigmaSubgroupsOfElement (g * x * g⁻¹)).ncard)
      ↔ (x ≠ 1 ∧ D.length x = 1 ∧ 1 < (maximalSigmaSubgroupsOfElement x).ncard) := by
    rw [D.length_one_iff, D.length_one_iff, hne1, hne_iff, hncard]
  by_cases hcase : x ≠ 1 ∧ D.length x = 1 ∧ 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · obtain ⟨hx, hlen, hgt⟩ := hcase
    obtain ⟨hxc, hlenc, hgtc⟩ := hcond_iff.mpr ⟨hx, hlen, hgt⟩
    obtain ⟨N, hNmax, hCN, hReq, _⟩ := exists_neighbor_Rsub_singleton hG D hlen hgt
    obtain ⟨N', _, _, hReq', hsing'⟩ := exists_neighbor_Rsub_singleton hG D hlenc hgtc
    have hNconj : MulAut.conj g • N = N' := by
      have hmem : MulAut.conj g • N
          ∈ maximalSubgroupsContaining (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) := by
        rw [mem_maximalSubgroupsContaining]
        refine ⟨mem_maximalSubgroups.mp
          (mem_maximalSubgroups_of_isConjugateSubgroup hNmax ⟨g, rfl⟩), ?_⟩
        rw [← smul_centralizer_singleton]
        intro y hy
        rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy ⊢
        exact hCN hy
      rw [hsing', Set.mem_singleton_iff] at hmem
      exact hmem
    rw [hReq', hReq, Subgroup.smul_inf, ← Msigma_conj_smul, smul_centralizer_singleton, hNconj]
  · have h1 : Rsub hG D (g * x * g⁻¹) = ⊥ := by
      rw [Rsub, dif_neg (fun h => hcase (hcond_iff.mp h))]
    have h2 : Rsub hG D x = ⊥ := by rw [Rsub, dif_neg hcase]
    rw [h1, h2, Subgroup.smul_bot]

/-- The left coset `x R(x)` as a pointwise scalar action: `x • R = { x r | r ∈ R }`.  Bridges
the set-builder form used by `xRsub_disjoint` to the `x • (R : Set G)` form on which the
pointwise-cardinality lemmas (`Set.ncard_smul_set`) act. -/
private theorem smul_coe_eq_coset (x : G) (R : Subgroup G) :
    x • (R : Set G) = {g : G | ∃ r ∈ R, g = x * r} := by
  ext g
  rw [Set.mem_smul_set]
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, smul_eq_mul]
  constructor
  · rintro ⟨r, hr, h⟩; exact ⟨r, hr, h.symm⟩
  · rintro ⟨r, hr, h⟩; exact ⟨r, hr, h.symm⟩

/-- **The cover** (BG mmd L3933, Lemma 14.5(c) Part B): the conjugacy saturation of `M̃` is the
disjoint union of the cosets `x R(x)` over `x ∈ 𝒞_G(M_σ^#)`.  By `R`-equivariance (`Rsub_conj`),
conjugating a product `x x'` (`x ∈ M_σ^#`, `x' ∈ R(x)`) by `g` gives `(xᵍ)(x'ᵍ)` with
`x'ᵍ ∈ R(xᵍ)` and `xᵍ ∈ 𝒞_G(M_σ^#)`, and conversely. -/
theorem conjClassSet_Mtilde_eq_biUnion [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} :
    conjClassSet (Mtilde hG D M)
      = ⋃ x ∈ sigmaConjugacySaturation M, x • (Rsub hG D x : Set G) := by
  ext y
  simp only [mem_conjClassSet, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, g, rfl⟩
    obtain ⟨x, hxsharp, x', hx'R, rfl⟩ := hm
    refine ⟨g * x * g⁻¹, ⟨x, hxsharp, g, rfl⟩, ?_⟩
    rw [Set.mem_smul_set]
    have hmem : g * x' * g⁻¹ ∈ Rsub hG D (g * x * g⁻¹) := by
      rw [Rsub_conj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hcalc : (MulAut.conj g)⁻¹ • (g * x' * g⁻¹) = x' := by
        rw [← map_inv (MulAut.conj) g, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
      rw [hcalc]; exact hx'R
    exact ⟨g * x' * g⁻¹, hmem, by rw [smul_eq_mul]; group⟩
  · rintro ⟨z, hz, hy⟩
    rw [Set.mem_smul_set] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [sigmaConjugacySaturation, mem_conjClassSet] at hz
    obtain ⟨t, ht, a, rfl⟩ := hz
    have hr' : r ∈ Rsub hG D (a * t * a⁻¹) := hr
    rw [Rsub_conj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hr'
    set s : G := (MulAut.conj a)⁻¹ • r with hs
    have hrs : r = a * s * a⁻¹ := by
      rw [hs, ← map_inv (MulAut.conj) a, MulAut.smul_def, MulAut.conj_apply, inv_inv]; group
    refine ⟨t * s, ⟨t, ht, s, hr', rfl⟩, a, ?_⟩
    rw [smul_eq_mul, hrs]; group

/-- **BG Lemma 14.5(c)** (mmd L3933-3940): `|𝒞_G(M̃)| = (|M_σ| − 1)·[G : M]`.  Combines Part B
(the disjoint cover `𝒞_G(M̃) = ⊔ₓ x R(x)`, giving `|𝒞_G(M̃)| = ∑ₓ |R(x)|` via 14.5(a) +
left-translation) with Part A (`sigmaSaturation_Rsub_count`: `∑ₓ |R(x)| = |M_σ^#|·[G : M]`).
This is the type-`P` counting bound that drives Theorem 14.7. -/
theorem sigmaConjugacySaturation_Mtilde_ncard [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    (conjClassSet (Mtilde hG D M)).ncard
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) - 1) * M.index := by
  classical
  have hdisj : (sigmaConjugacySaturation M).PairwiseDisjoint
      (fun x => x • (Rsub hG D x : Set G)) := by
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [smul_coe_eq_coset, smul_coe_eq_coset]
    exact xRsub_disjoint hG D
      (length_one_of_mem_sigmaConjugacySaturation hG D hM hx).1
      (length_one_of_mem_sigmaConjugacySaturation hG D hM hy).1 hxy
  have key : (⋃ x ∈ sigmaConjugacySaturation M, x • (Rsub hG D x : Set G)).ncard
      = ∑ x ∈ (Set.toFinite (sigmaConjugacySaturation M)).toFinset,
          Nat.card ↥(Rsub hG D x) := by
    rw [(Set.toFinite (sigmaConjugacySaturation M)).ncard_biUnion
        (fun i _ => Set.toFinite _) hdisj, ← finsum_mem_coe_finset]
    refine finsum_mem_congr (Set.Finite.coe_toFinset _).symm (fun x _ => ?_)
    rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.refl _)
  have hsharp : (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)).ncard
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) - 1 := by
    have hc : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)
        = (OddOrder.BG.Ch3.S10.Msigma M : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
    rw [sharpSubgroup, Set.ncard_sdiff
        (Set.singleton_subset_iff.mpr (OddOrder.BG.Ch3.S10.Msigma M).one_mem),
      Set.ncard_singleton, hc]
  rw [conjClassSet_Mtilde_eq_biUnion hG D, key, sigmaSaturation_Rsub_count hG D hM, hsharp]

/-- **BG Lemma 14.5(b)** (mmd L3875): for nonconjugate maximal `M`, `N`, the conjugacy
saturations `𝒞_G(M̃)`, `𝒞_G(Ñ)` are disjoint — a counting-separation lemma feeding
Theorem 14.7 and Corollary 14.9.

**Proof (2026-06-14):** PROVED, citing only Theorem 13.9 (`sigma_disjoint_of_nonconjugate`).
**Now fully unconditional (2026-06-15):** Theorem 13.9 landed in §13 (Lane F), so 14.5 is
sorry-free and axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`;
registered in `AxiomsCheck`).  It is the first §14 result beyond Lemma 14.1 to go green.
The `M_σ^#` restriction turns out to be a *feature* here: if `g` is conjugate to both
`t ∈ M_σ^#` and `s ∈ N_σ^#`, then
`t` and `s` are conjugate, so `orderOf t = orderOf s`; a prime `p` dividing it lies in `σ(M)`
(as `M_σ` is a `σ(M)`-group) and in `σ(N)`, contradicting `σ(M) ∩ σ(N) = ∅`. No `R(x)` / `M̃`
machinery is needed — **13.9 alone suffices**.

**Faithfulness note (2026-06-14):** the Lean surface uses `sigmaConjugacySaturation =
𝒞_G(M_σ^#)` rather than BG's `𝒞_G(M̃)` (see `sigmaSharp`). Since `M_σ^# ⊆ M̃`, this is a
**true but weaker** restriction of BG 14.5(b); it does **not** capture the `ℓ_σ = 2` twisted
elements of `M̃`. Lemma 14.5(a) (`x R(x)` disjoint from `y R(y)`) and (c) (the count
`|𝒞_G(M̃)| = (|M_σ| − 1)|G:M|`) are not stated here (need `R(x)`, gated on §13). -/
theorem sigmaConjugacy_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    (hnc : ¬ IsConjugateSubgroup M N) :
    Disjoint (sigmaConjugacySaturation M) (sigmaConjugacySaturation N) := by
  -- Theorem 13.9: nonconjugate maximal subgroups have disjoint `σ`-sets.
  have hσ : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma N) :=
    sigma_disjoint_of_nonconjugate hG hM hN hnc
  -- Every prime dividing the order of a nonidentity `M_σ`-element lies in `σ(M)`
  -- (because `M_σ` is a `σ(M)`-group).
  have bridge : ∀ (L : Subgroup G) (x : G), x ∈ OddOrder.BG.Ch3.S10.Msigma L →
      ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ OddOrder.BG.Ch3.S10.sigma L := by
    intro L x hxL p hp hpx
    have hdvd : orderOf x ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma L) :=
      (OddOrder.BG.Ch3.S10.Msigma L).orderOf_dvd_natCard hxL
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup L p
      (Nat.mem_primeFactors.mpr ⟨hp, hpx.trans hdvd, Nat.card_pos.ne'⟩)
  rw [Set.disjoint_left]
  rintro g hgM hgN
  simp only [sigmaConjugacySaturation, sigmaSharp, sharpSubgroup, mem_conjClassSet,
    Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hgM hgN
  obtain ⟨t, ⟨htM, ht1⟩, a, hat⟩ := hgM
  obtain ⟨s, ⟨hsN, _hs1⟩, b, hbs⟩ := hgN
  -- `t` is conjugate to `s` (both conjugate to `g`), hence has the same order.
  have heq : a * t * a⁻¹ = b * s * b⁻¹ := hat.trans hbs.symm
  have hconj : (a⁻¹ * b) * s * (a⁻¹ * b)⁻¹ = t := by
    have h2 : (a⁻¹ * b) * s * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * s * b⁻¹) * a := by group
    rw [h2, ← heq]; group
  have hsc : SemiconjBy (a⁻¹ * b) s t := mul_inv_eq_iff_eq_mul.mp hconj
  have hts : orderOf t = orderOf s := (SemiconjBy.orderOf_eq (a⁻¹ * b) hsc).symm
  -- A prime `p ∣ orderOf t` then lies in `σ(M) ∩ σ(N)`, contradicting Theorem 13.9.
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (fun h => ht1 (orderOf_eq_one_iff.mp h))
  exact Set.disjoint_left.mp hσ (bridge M t htM p hp hpt) (bridge N s hsN p hp (hts ▸ hpt))

/-- **BG Lemma 14.6, exclusivity** (mmd L3947): the `type-2 ⟹ ¬type-1` direction that Theorem 14.7
consumes as "`T ∩ H̃` is empty".  If `g = y·y'` with `y ∈ M_σ^#` (hence `ℓ_σ(y) = 1`) and `y'` a
nonidentity `κ(M)`-element of `C_M(y)`, then `g` is **not** of the form `x·x'` with `ℓ_σ(x) = 1`
and `x' ∈ R(x)`.  Mirrors Lemma 14.5(a)'s factor matching (`isPiElement_mul_unique` + the σ-class
partition); the contradiction is `κ(M)` (`p`-rank 1) vs `τ₂(N)` (`p`-rank 2) for the factor
`x = y'`, using that `p`-rank is conjugation invariant. -/
theorem not_type1_of_type2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {g : G} {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {y y' : G} (hy : y ∈ sigmaSharp M) (hgyy' : g = y * y') (hcomm : Commute y y')
    (hy'1 : y' ≠ 1) (hy'M : y' ∈ M) (hy'C : y' ∈ Subgroup.centralizer ({y} : Set G))
    (hy'κ : ∀ p ∈ piSet (Subgroup.closure {y'}), p ∈ kappa M) :
    ¬ ∃ x x' : G, g = x * x' ∧ D.length x = 1 ∧ x' ∈ Rsub hG D x := by
  classical
  rintro ⟨x, x', hgxx', hlx, hx'R⟩
  have hx1 : x ≠ 1 := ((D.length_one_iff x).mp hlx).1
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hy
  obtain ⟨hyMσ, hy1⟩ := hy
  have hgeq : x * x' = y * y' := hgxx'.symm.trans hgyy'
  have hpiSet : ∀ z : G, ∀ {q : ℕ}, q ∈ (orderOf z).primeFactors →
      q ∈ piSet (Subgroup.closure ({z} : Set G)) := fun z {q} hq => by
    rw [piSet, Set.mem_setOf_eq, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]; exact hq
  obtain ⟨M_x, hMxmax, hxMx⟩ := ((D.length_one_iff x).mp hlx).2
  have hxPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) x := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M_x p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans
        ((OddOrder.BG.Ch3.S10.Msigma M_x).orderOf_dvd_natCard hxMx), Nat.card_pos.ne'⟩)
  have hyPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) y := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans
        ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hyMσ), Nat.card_pos.ne'⟩)
  have hx'Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hlx ⟨hMxmax, hxMx⟩ hx'R
  have hy'Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ y' := by
    intro p hp hpM
    rcases (hy'κ p (hpiSet y' hp)).2.1 with h1 | h3
    · exact tau1_subset_sigma_compl M h1 hpM
    · exact tau3_subset_sigma_compl M h3 hpM
  have hcx : Commute x x' :=
    Subgroup.mem_centralizer_iff.mp (Rsub_le_centralizer hG D x hx'R) x (Set.mem_singleton x)
  -- `x' ≠ 1`: else `g = x` collides with `g = y·y'`, `y' ≠ 1`.
  have hx'1 : x' ≠ 1 := by
    intro hx'0
    rw [hx'0, mul_one] at hgeq
    by_cases hσ : OddOrder.BG.Ch3.S10.sigma M_x = OddOrder.BG.Ch3.S10.sigma M
    · have hxPiM : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x := by
        rw [← hσ]; exact hxPi
      exact hy'1 (OddOrder.GroupTheory.isPiElement_mul_unique (mul_one x) (Commute.one_right x)
        hxPiM (OddOrder.GroupTheory.isPiElement_one _) hgeq.symm hcomm hyPi hy'Pi).2.symm
    · have hxPiMc : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x :=
        fun p hp hpM => hσ (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hM (hxPi p hp) hpM)
      exact hy1 (OddOrder.GroupTheory.isPiElement_mul_unique (one_mul x) (Commute.one_left x)
        (OddOrder.GroupTheory.isPiElement_one _) hxPiMc hgeq.symm hcomm hyPi hy'Pi).1.symm
  have hgtx : 1 < (maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    rw [Rsub, dif_neg (fun hc => h hc.2.2), Subgroup.mem_bot] at hx'R
    exact hx'1 hx'R
  obtain ⟨N, hNmax, hCxN, hReqN, hπτ2N, _⟩ := exists_neighbor_eq_Rsub hG D hlx hgtx
  have hxN : x ∈ N := hCxN (Subgroup.mem_centralizer_iff.mpr fun z hz => by
    rw [Set.mem_singleton_iff.mp hz])
  have hRxne : OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    rw [← hReqN]; intro hbot; exact hx'1 (Subgroup.mem_bot.mp (hbot ▸ hx'R))
  have hsingx : maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} :=
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx1 hπτ2N hRxne
  by_cases hσeq : OddOrder.BG.Ch3.S10.sigma M_x = OddOrder.BG.Ch3.S10.sigma M
  · -- **Equal classes**: `x = y`; then `M = N` and `x = y ∈ M_σ` is a `τ₂(M)`-element, absurd.
    have hyPiMx : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) y := by
      rw [hσeq]; exact hyPi
    have hy'PiMxc : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ y' := by
      rw [hσeq]; exact hy'Pi
    have hxy : x = y :=
      (OddOrder.GroupTheory.isPiElement_mul_unique rfl hcx hxPi hx'Pi hgeq.symm hcomm
        hyPiMx hy'PiMxc).1
    -- Corollary 14.3 for `(y, y')`: branch 2 (`τ₂`) is impossible, so `C_G(y) ⊆ M`.
    have hCyM : Subgroup.centralizer ({y} : Set G) ≤ M := by
      have hyσsharp : y ∈ sigmaSharp M := by
        rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
        exact ⟨hyMσ, hy1⟩
      rcases sigma_diagnostic hG D hM hyσsharp hy'M hy'1 hy'C
        (fun p hp => hy'Pi p (by
          rw [piSet, Set.mem_setOf_eq, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers] at hp
          exact hp)) with ⟨_, hsub⟩ | ⟨hτ2, _, _⟩
      · exact hsub
      · exfalso
        obtain ⟨q, hqy⟩ : (orderOf y').primeFactors.Nonempty :=
          Nat.nonempty_primeFactors.mpr (by
            have := orderOf_pos y'; have hne : orderOf y' ≠ 1 := fun h => hy'1 (orderOf_eq_one_iff.mp h)
            omega)
        have hqκ := hy'κ q (hpiSet y' hqy)
        have hqτ2 := hτ2 q (hpiSet y' hqy)
        rcases hqκ.2.1 with h1 | h3
        · exact absurd ((tau1_pRank_eq_one h1).symm.trans (tau2_pRank_eq_two hqτ2)) (by norm_num)
        · exact absurd ((tau3_pRank_eq_one h3).symm.trans (tau2_pRank_eq_two hqτ2)) (by norm_num)
    have hMN : M = N := by
      have hmem : M ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
        mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hxy ▸ hCyM⟩
      rw [hsingx, Set.mem_singleton_iff] at hmem; exact hmem
    obtain ⟨p, hpx⟩ : (orderOf x).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := orderOf_pos x; have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h); omega)
    have hpτ2M : p ∈ tau2 M := hMN ▸ hπτ2N p (hpiSet x hpx)
    have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hxy ▸ hyMσ
    have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hpx, (Nat.dvd_of_mem_primeFactors hpx).trans
          ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hxMσ), Nat.card_pos.ne'⟩)
    exact tau2_subset_sigma_compl M hpτ2M hpσM
  · -- **Disjoint classes**: factor matching gives `y = x'`, `y' = x`; then `M, N` conjugate, and
    -- `x = y'` is a `κ(M)`-element (rank 1) and a `τ₂(N)`-element (rank 2), absurd by conj-invariance.
    have hxPiMc : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x :=
      fun p hp hpM => hσeq (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hM (hxPi p hp) hpM)
    have hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N := by
      rw [hReqN] at hx'R; exact (Subgroup.mem_inf.mp hx'R).1
    have hx'PiN : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N) x' := fun q hq =>
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup N q (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hq, (Nat.dvd_of_mem_primeFactors hq).trans
          ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hx'N), Nat.card_pos.ne'⟩)
    obtain ⟨p, hpy⟩ : (orderOf y).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := orderOf_pos y; have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h); omega)
    have hcox : Nat.Coprime (orderOf x) (orderOf x') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hxPi hx'Pi
    have hpg : (orderOf (x * x')).primeFactors =
        (orderOf x).primeFactors ∪ (orderOf x').primeFactors := by
      rw [hcx.orderOf_mul_eq_mul_orderOf_of_coprime hcox,
        Nat.primeFactors_mul (orderOf_pos x).ne' (orderOf_pos x').ne']
    have hcoy : Nat.Coprime (orderOf y) (orderOf y') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hyPi hy'Pi
    have hyg : (orderOf y).primeFactors ⊆ (orderOf (x * x')).primeFactors := by
      rw [hgeq, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcoy,
        Nat.primeFactors_mul (orderOf_pos y).ne' (orderOf_pos y').ne']
      exact Finset.subset_union_left
    have hpmem : p ∈ (orderOf x).primeFactors ∪ (orderOf x').primeFactors := hpg ▸ hyg hpy
    have hσMN : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma N := by
      rcases Finset.mem_union.mp hpmem with hpx | hpx'
      · exact absurd (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hM (hxPi p hpx) (hyPi p hpy)) hσeq
      · exact sigma_eq_of_mem_sigma_of_mem_sigma hG hM hNmax (hyPi p hpy) (hx'PiN p hpx')
    have hx'PiM : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x' := by
      rw [hσMN]; exact hx'PiN
    obtain ⟨hx'y, hxy'⟩ := OddOrder.GroupTheory.isPiElement_mul_unique (g := x * x')
      hcx.symm hcx.symm hx'PiM hxPiMc hgeq.symm hcomm hyPi hy'Pi
    -- `M, N` conjugate (`y ∈ M_σ ∩ N_σ`, `σ(M) = σ(N)`, Thm 13.9).
    have hconj : IsConjugateSubgroup M N := by
      by_contra hnc
      exact Set.disjoint_left.mp (sigma_disjoint_of_nonconjugate hG hM hNmax hnc)
        (hyPi p hpy) (hσMN ▸ hyPi p hpy)
    -- `x = y'` is a `κ(M)`-element and a `τ₂(N)`-element; `p`-rank is conjugation invariant.
    obtain ⟨p2, hp2x⟩ : (orderOf x).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := orderOf_pos x; have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h); omega)
    have hp2κ : p2 ∈ kappa M := hy'κ p2 (hxy' ▸ hpiSet x hp2x)
    have hp2τ2 : p2 ∈ tau2 N := hπτ2N p2 (hpiSet x hp2x)
    have hrM : pRank ↥M p2 = 1 := by
      rcases hp2κ.2.1 with h1 | h3
      · exact tau1_pRank_eq_one h1
      · exact tau3_pRank_eq_one h3
    have hrN : pRank ↥N p2 = 2 := tau2_pRank_eq_two hp2τ2
    obtain ⟨c, hc⟩ := hconj
    have hmapN : M.map (MulAut.conj c).toMonoidHom = N := hc
    have heq : pRank ↥M p2 = pRank ↥N p2 :=
      pRank_eq_of_mulEquiv
        ((Subgroup.equivMapOfInjective M (MulAut.conj c).toMonoidHom
          (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmapN))
    rw [hrM, hrN] at heq
    exact absurd heq (by norm_num)

/-- **Conjugacy-saturation count of a TI-subset** (BG §1, the input to Theorem 14.7 step 5):
for a TI-subset `A` with normalizer-bound `L` that `L` stabilizes (`A^l = A` for `l ∈ L`), the
saturation `𝒞_G(A)` is the disjoint union of the `[G:L]` conjugates `A^g` (each of cardinality
`|A|`), whence `|𝒞_G(A)| = |A|·[G:L]`.  The subset analogue of
`ncard_conjugates_eq_index_of_normalizer_eq_self`. -/
theorem ncard_conjClassSet_of_isTISubset [Finite G] {A : Set G} {L : Subgroup G}
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A) :
    (conjClassSet A).ncard = A.ncard * L.index := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hwd : ∀ g₁ g₂ : G, QuotientGroup.leftRel L g₁ g₂ →
      MulAut.conj g₁ • A = MulAut.conj g₂ • A := by
    intro g₁ g₂ hrel
    rw [QuotientGroup.leftRel_apply] at hrel
    calc MulAut.conj g₁ • A
        = MulAut.conj g₁ • (MulAut.conj (g₁⁻¹ * g₂) • A) := by rw [hstab _ hrel]
      _ = MulAut.conj g₂ • A := by rw [← mul_smul, ← map_mul, mul_inv_cancel_left]
  set B : G ⧸ L → Set G := Quotient.lift (fun g => MulAut.conj g • A) hwd with hBdef
  have hBval : ∀ g : G, B (QuotientGroup.mk g) = MulAut.conj g • A := fun g => rfl
  have hunion : conjClassSet A = ⋃ q : G ⧸ L, B q := by
    ext y
    rw [mem_conjClassSet, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, g, rfl⟩
      refine ⟨QuotientGroup.mk g, ?_⟩
      rw [hBval, Set.mem_smul_set]
      exact ⟨t, ht, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    · rintro ⟨q, hq⟩
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      rw [hBval, Set.mem_smul_set] at hq
      obtain ⟨a, ha, rfl⟩ := hq
      exact ⟨a, ha, g, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro q q' hqq'
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨g', rfl⟩ := Quotient.exists_rep q'
    simp only [Function.onFun, hBval]
    rw [Set.disjoint_left]
    rintro y hy hy'
    rw [Set.mem_smul_set] at hy hy'
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨a', ha', heq⟩ := hy'
    have he : g * a * g⁻¹ = g' * a' * g'⁻¹ := by
      rw [MulAut.smul_def, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply] at heq
      exact heq.symm
    have hov : (g'⁻¹ * g) * a * (g'⁻¹ * g)⁻¹ ∈ A := by
      have hc : (g'⁻¹ * g) * a * (g'⁻¹ * g)⁻¹ = a' := by
        rw [show (g'⁻¹ * g) * a * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * a * g⁻¹) * g' from by group, he]; group
      rw [hc]; exact ha'
    have hmem : g'⁻¹ * g ∈ L := hTI (g'⁻¹ * g) ⟨a, ha, hov⟩
    apply hqq'
    apply Quotient.sound
    change (QuotientGroup.leftRel L) g g'
    rw [QuotientGroup.leftRel_apply]
    have h2 : g⁻¹ * g' = (g'⁻¹ * g)⁻¹ := by group
    rw [h2]; exact L.inv_mem hmem
  rw [hunion, Set.ncard_iUnion_of_finite (fun q => Set.toFinite _) hdisj]
  have hBcard : ∀ q : G ⧸ L, (B q).ncard = A.ncard := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    rw [hBval]; exact Set.ncard_smul_set _ _
  rw [finsum_congr hBcard, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card, ← Subgroup.index]
  exact mul_comm _ _

/-! ## Theorem 14.7 through Lemma 14.13: type-P duality and global counting -/

/-! ### `Z = K ⊔ K*` internal direct product (BG 14.7 bedrock)

For a type-`P` maximal `M`, a Hall `κ(M)`-subgroup `K`, and `K* = C_{M_σ}(K)`, the join
`Z = K ⊔ K*` is the *internal direct product* of `K` and `K*`: their orders are coprime
(`K` a `σ(M)'`-group since `κ(M) ⊆ σ(M)'`, `K* ≤ M_σ` a `σ(M)`-group), and they commute
(`K* ≤ C_G(K)`).  Hence `K ⊓ K* = 1`, `|Z| = |K|·|K*|`, and — once both factors are cyclic
(which the §14 counting collapse forces, BG L4041) — `Z` is cyclic.

These are the *ungated* structural facts underlying the density count of Theorem 14.7(e)
(`|𝒞_G(Ẑ)| = (1 - 1/k - 1/k* + 1/kk*)|G|`, mmd L4031-4045) and the `IsCyclic (K ⊔ K*)`
conjunct (d).  They depend only on `K` being a Hall `κ(M)`-subgroup and `K* = C_{M_σ}(K)`,
not on the type-P duality counting itself. -/

/-- A Hall `κ(M)`-subgroup `K` is a `σ(M)'`-subgroup (since `κ(M) ⊆ σ(M)'`).  Extracted from
the `hK_pi` step internal to `typeP_structure` for reuse in the `Z`-structure lemmas. -/
theorem kappaHall_isPiSubgroup_sigmaCompl {M K : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
  intro p hp
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
  exact kappa_subset_sigmaCompl (hK.1 p hp)

/-- `K* = C_{M_σ}(K)` is a `σ(M)`-subgroup (it lies in `M_σ`, a `σ(M)`-group). -/
theorem Kstar_isPiSubgroup_sigma [Finite G] {M K Kstar : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar := by
  intro p hp
  have hle : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := hKstar ▸ inf_le_left
  obtain ⟨hpp, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
  refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
    ⟨hpp, hpdvd.trans (Subgroup.card_dvd_of_le hle), Nat.card_pos.ne'⟩)

/-- **BG 14.7, `|K|`, `|K*|` coprime** (mmd L4027): `K` is a `σ(M)'`-group, `K* ≤ M_σ` a
`σ(M)`-group, so no prime divides both. -/
theorem coprime_card_kappaHall_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) := by
  apply Nat.coprime_of_dvd
  intro p hp hpK hpKstar
  have hpσc : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    kappaHall_isPiSubgroup_sigmaCompl hKM hK p
      (Nat.mem_primeFactors.mpr ⟨hp, hpK, Nat.card_pos.ne'⟩)
  exact hpσc (Kstar_isPiSubgroup_sigma hKstar p
    (Nat.mem_primeFactors.mpr ⟨hp, hpKstar, Nat.card_pos.ne'⟩))

/-- **BG 14.7, `|K| > 1`**: the κ-Hall factor of a type-`P` maximal subgroup is nontrivial.  Some
prime `p ∈ κ(M)` divides `|K|`: `p` divides `|M|` (it is the order of an elementary abelian
`p`-subgroup of `M`, by the definition of `κ`), and is coprime to the Hall index `[M : K]`, so it
divides the Hall order `|K|`. -/
theorem card_kappaHall_ne_one [Finite G] {M K : Subgroup G} (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) :
    Nat.card ↥K ≠ 1 := by
  obtain ⟨p, hpκ⟩ := hP
  have hpprime : p.Prime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  exact fun h => hpprime.ne_one (Nat.dvd_one.mp (h ▸ hpK))

/-- **BG 14.7, `|K| ≠ |K*|`**: the two κ-Hall factors of a type-`P` dual pair have distinct orders.
They are coprime (`coprime_card_kappaHall_Kstar`) and `|K| > 1` (`card_kappaHall_ne_one`), so equality
would force `|K| = 1`. -/
theorem card_kappaHall_ne_card_Kstar [Finite G] {M K Kstar : Subgroup G} (hP : IsTypeP M)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥K ≠ Nat.card ↥Kstar := by
  intro heq
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) :=
    coprime_card_kappaHall_Kstar hKM hK hKstar
  rw [← heq, Nat.Coprime, Nat.gcd_self] at hcop
  exact card_kappaHall_ne_one hP hKM hK hcop

/-- **BG 14.7, `K ⊓ K* = 1`**: the coprime factors meet trivially. -/
theorem kappaHall_inf_Kstar_eq_bot [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    K ⊓ Kstar = ⊥ :=
  Subgroup.inf_eq_bot_of_coprime (coprime_card_kappaHall_Kstar hKM hK hKstar)

/-- **BG 14.7, `K*` centralizes `K`**: every element of `K` commutes with every element of
`K* = C_{M_σ}(K)` (which lies in `C_G(K)`). -/
theorem commute_kappaHall_Kstar {M K Kstar : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ (a : ↥K) (b : ↥Kstar), Commute (K.subtype a) (Kstar.subtype b) := by
  intro a b
  have hb : (b : G) ∈ Subgroup.centralizer (K : Set G) := by
    have hbmem : (b : G) ∈
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) := by
      rw [← hKstar]; exact b.2
    exact (Subgroup.mem_inf.mp hbmem).2
  exact Subgroup.mem_centralizer_iff.mp hb (a : G) a.2

/-- **BG 14.7, `Z = K × K*` internal direct product iso** `↥K × ↥K* ≃* ↥(K ⊔ K*)`,
`(a, b) ↦ a·b` (well-defined since `K`, `K*` commute, injective since `K ⊓ K* = 1`). -/
noncomputable def kappaHall_prod_Kstar_mulEquiv [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (↥K × ↥Kstar) ≃* ↥(K ⊔ Kstar) := by
  have hcomm := commute_kappaHall_Kstar hKstar
  have hinj : Function.Injective (MonoidHom.noncommCoprod K.subtype Kstar.subtype hcomm) :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨K.subtype_injective, Kstar.subtype_injective, by
        rw [K.range_subtype, Kstar.range_subtype]
        exact disjoint_iff.mpr (kappaHall_inf_Kstar_eq_bot hKM hK hKstar)⟩
  have hrange : (MonoidHom.noncommCoprod K.subtype Kstar.subtype hcomm).range = K ⊔ Kstar := by
    rw [MonoidHom.noncommCoprod_range, K.range_subtype, Kstar.range_subtype]
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

/-- **BG 14.7, `|Z| = |K|·|K*|`** (mmd L4029, `z = k k*`): the internal direct product order. -/
theorem card_kappaHall_sup_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar := by
  rw [← Nat.card_congr (kappaHall_prod_Kstar_mulEquiv hKM hK hKstar).toEquiv, Nat.card_prod]

/-- **BG 14.7(d), `Z = K ⊔ K*` cyclic** (mmd L4041): once both factors are cyclic (forced by the
counting collapse `n = 1`, where `r(K) = r(K*) = 1`), the coprime commuting product is cyclic. -/
theorem isCyclic_kappaHall_sup_Kstar_of_cyclic [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    [IsCyclic ↥K] [IsCyclic ↥Kstar] :
    IsCyclic ↥(K ⊔ Kstar) := by
  have hprodcyc : IsCyclic (↥K × ↥Kstar) :=
    Group.isCyclic_prod_iff.mpr
      ⟨inferInstance, inferInstance, coprime_card_kappaHall_Kstar hKM hK hKstar⟩
  exact (kappaHall_prod_Kstar_mulEquiv hKM hK hKstar).isCyclic.mp hprodcyc

/-- **BG 14.7(h), coprimality is free given the complement**: if `M' = [M,M]` complements the
Hall `κ(M)`-subgroup `K` in `M`, then `|M'|` and `|K|` are coprime — `|M'| = [M : K]` (from the
complement) and a Hall subgroup has order coprime to its index.  This reduces Theorem 14.7(h) to its
substantive obligation `IsComplement' M' K` (mmd L4061, which consumes "`K` cyclic" from the
counting collapse); the second conjunct then follows with no further input. -/
theorem coprime_card_derived_kappaHall_of_isComplement' [Finite G] {M K : Subgroup G}
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hc : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)) :
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) := by
  have hcop := hK.coprime_index
  rw [hc.index_eq_card] at hcop
  exact hcop.symm

/-- **Counting-bound kernel for Theorem 14.7(e)** (BG mmd L3975, the `8/15 > 1/2` step).
For `k ≥ 3` and `k* ≥ 5`, the saturation density `(1 - 1/k)(1 - 1/k*)` exceeds `1/2`
(minimised at `(1 - 1/3)(1 - 1/5) = 8/15`).  In Theorem 14.7, `k = |K|` and `k* = |K*|` are
coprime odd integers `> 1` (so `{k, k*} ⊇ {3, 5}` in the worst case), and
`|𝒞_G(Ẑ)| = (1 - 1/k)(1 - 1/k*)|G|`; this bound gives `|𝒞_G(Ẑ)| > ½|G|`, forcing every type-P
maximal subgroup to be conjugate to `M` or `M*`.  Pure arithmetic, independent of §13. -/
theorem half_lt_one_sub_inv_mul {k l : ℕ} (hk : 3 ≤ k) (hl : 5 ≤ l) :
    (1 : ℚ) / 2 < (1 - 1 / (k : ℚ)) * (1 - 1 / (l : ℚ)) := by
  have hk3 : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hl5 : (5 : ℚ) ≤ (l : ℚ) := by exact_mod_cast hl
  have hik : 1 / (k : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
  have hil : 1 / (l : ℚ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hl5
  calc (1 : ℚ) / 2 < (2 / 3) * (4 / 5) := by norm_num
    _ ≤ (1 - 1 / (k : ℚ)) * (1 - 1 / (l : ℚ)) :=
        mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)

/-- **BG Theorem 14.7, partner existence** (§16-independent core, mmd L3975-3991): for a type-`P`
maximal `M` with Hall `κ(M)`-subgroup `K`, `Kstar = C_{M_σ}(K)`, and a line `X ∈ ℰ_p¹(K)`, every
`M* ∈ 𝓜(N_G(X))` (which exists, `N_G(X)` being proper) is type-`P`, nonconjugate to `M`, contains
`K ⊔ Kstar` with `X ≤ M*_σ`, and `π(Kstar) ⊆ κ(M*)`.  This is the nonconjugate partner `M*` of
Theorem 14.7 with its basic neighbour data; cyclicity of `Z`, the TI property, type-`P₂`, and the
§16-gated covering/uniqueness are layered on top.  Built from `typeP_neighbor_embed` +
`typeP_neighbor_kappa` (the §16-independent pre-position, steps 1a/1b). -/
theorem exists_typeP_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K) :
    ∃ Mstar : Subgroup G,
      Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ∧
      ¬ IsConjugateSubgroup M Mstar ∧ K ⊔ Kstar ≤ Mstar ∧
      X ≤ OddOrder.BG.Ch3.S10.Msigma Mstar ∧
      (∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mstar) ∧ IsTypeP Mstar := by
  classical
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  -- `C_{M_σ}(X) ⊇ C_{M_σ}(K) = Kstar ≠ 1`.
  have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
    intro hbot
    refine hKstarne (le_bot_iff.mp ?_)
    rw [hKstar]
    calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
        ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
          inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
      _ = ⊥ := hbot
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hX
  obtain ⟨Mstar, hMstarmax, hMstarge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hM hXne (hXK.trans hKM)
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstarmax, hMstarge⟩
  obtain ⟨hnc, hZle, hXMsσ⟩ :=
    typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hMstarmem
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hMstarmem
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  exact ⟨Mstar, hMstarmem, hnc, hZle, hXMsσ, hκ, ⟨q, hκ q hq⟩⟩

/-- **σ-part lands in the σ-factor of an internal direct product**: in `Ki ⊔ Kistar`, where `Kistar`
centralizes `Ki`, `Kistar ≤ M_σ`, and `Ki ⊓ M_σ = ⊥` (e.g. `Ki` is a `σ(Mi)'`-group), any subgroup
`X ≤ Ki ⊔ Kistar` contained in `M_σ` lies in `Kistar`.  Writing `x = a·b` (`a ∈ Ki`, `b ∈ Kistar`),
the `σ'`-part `a = x·b⁻¹ ∈ M_σ ⊓ Ki = ⊥`, so `x = b ∈ Kistar`.  This is the `σ`-projection used by
the swap argument (BG mmd L3999, "it follows that `X_i ⊆ K_i*`") and the `Z`-decomposition. -/
theorem le_centralizerFactor_of_le_sup_of_le_Msigma [Finite G] {Mi Ki Kistar X : Subgroup G}
    (hKistarC : Kistar ≤ Subgroup.centralizer (Ki : Set G))
    (hKistarMσ : Kistar ≤ OddOrder.BG.Ch3.S10.Msigma Mi)
    (hKiMσ : Ki ⊓ OddOrder.BG.Ch3.S10.Msigma Mi = ⊥)
    (hXsup : X ≤ Ki ⊔ Kistar) (hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma Mi) :
    X ≤ Kistar := by
  classical
  -- `Ki` is normal in `Ki ⊔ Kistar` (`Kistar` centralizes it), so elements decompose as `a · b`.
  have hKnorm : Ki ⊔ Kistar ≤ Subgroup.normalizer (Ki : Set G) :=
    sup_le Subgroup.le_normalizer (hKistarC.trans (Subgroup.centralizer_le_normalizer _))
  haveI : ((Ki).subgroupOf (Ki ⊔ Kistar)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnorm
  have hsuptop : (Ki.subgroupOf (Ki ⊔ Kistar)) ⊔ (Kistar.subgroupOf (Ki ⊔ Kistar)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hsuptop ▸ Subgroup.mem_top (⟨x, hXsup hx⟩ : ↥(Ki ⊔ Kistar)))
  have haKi : (a : G) ∈ Ki := Subgroup.mem_subgroupOf.mp ha
  have hbKistar : (b : G) ∈ Kistar := Subgroup.mem_subgroupOf.mp hb
  have hab' : (a : G) * (b : G) = x := by have := congrArg Subtype.val hab; simpa using this
  have haMσ : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma Mi := by
    have heq : (a : G) = x * (b : G)⁻¹ := by rw [← hab']; group
    rw [heq]
    exact (OddOrder.BG.Ch3.S10.Msigma Mi).mul_mem (hXMσ hx)
      ((OddOrder.BG.Ch3.S10.Msigma Mi).inv_mem (hKistarMσ hbKistar))
  have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (hKiMσ ▸ Subgroup.mem_inf.mpr ⟨haKi, haMσ⟩)
  rw [← hab', ha1, one_mul]; exact hbKistar

/-- **BG 14.7, neighbour normalizer identity** (Proposition 14.2(b1) packaged for a neighbour,
mmd L3997): for a type-`P` maximal `Mi`, a Hall `κ(Mi)`-subgroup `Ki ≤ Mi`, and a rank-one
`X ≤ Ki`, `N_G(X) ⊓ Mi = Ki ⊔ C_{Mi_σ}(Ki)`.  The Hall `(κ(Mi) ∪ σ(Mi))'`-subgroup that
Proposition 14.2 needs is produced internally via `hall_E_exists` (in the solvable group `↥Mi`),
so the swap argument supplies only `Ki` and `X`.  Applied twice — to `Ki` and to a Hall
`κ(Mi)`-subgroup `Ki' ⊇ K*` — it yields `Ki ⊔ Ki* = N_G(X) ⊓ Mi = Ki' ⊔ Ki'*`, the choice
independence at the heart of the swap. -/
theorem typeP_normalizer_inf_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mi Ki : Subgroup G} (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi))
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXKi : X ≤ Ki) :
    Subgroup.normalizer (X : Set G) ⊓ Mi =
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  haveI : IsSolvable ↥Mi := hG.solvable_of_mem_maximalSubgroups hMi
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUeq : (U'.map Mi.subtype).subgroupOf Mi = U' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((U'.map Mi.subtype).subgroupOf Mi) := by rw [hUeq]; exact hU'
  obtain ⟨_, _, hb1, _, _, _⟩ := typeP_structure hG hMi hPi hKiMi hKi rfl hU
  exact hb1 p hp X hX hXKi

/-- **BG 14.7, `M ⊇ N_G(X)` from a unique centralizer-maximal** (mmd L3992, "Moreover, `M ⊇
N_G(X)`"): if `M` is the *unique* maximal subgroup containing `C_G(X)` (i.e.
`ℳ(C_G(X)) = {M}`, the conclusion of Proposition 14.2(c)), then `N_G(X) ≤ M`.

For `g ∈ N_G(X)`, conjugation by `g` fixes `C_G(X)` (`g` normalizes `X`), so `Mᵍ` is again a
maximal subgroup containing `C_G(X)`; by uniqueness `Mᵍ = M`, hence `g ∈ N_G(M) = M`
(`M` self-normalizing as a maximal subgroup).  A general fact, independent of §13. -/
theorem normalizer_le_of_maximalSubgroupsContaining_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M X : Subgroup G}
    (hsing : maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  classical
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    rw [hsing]; rfl
  rw [mem_maximalSubgroupsContaining] at hMmem
  obtain ⟨hMcoat, hCXM⟩ := hMmem
  intro g hg
  -- `g` normalizes `X`, hence normalizes `C_G(X)`: `Mᵍ ⊇ C_G(X)ᵍ = C_G(X)`.
  have hgcent : MulAut.conj g • Subgroup.centralizer (X : Set G)
      = Subgroup.centralizer (X : Set G) := by
    have h1 : MulAut.conj g • Subgroup.centralizer (X : Set G)
        = Subgroup.centralizer ((MulAut.conj g • X : Subgroup G) : Set G) :=
      Subgroup.map_centralizer_eq_of_bijective (X : Set G) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).bijective
    rwa [OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer hg] at h1
  -- `Mᵍ` is a maximal subgroup containing `C_G(X)`, so by uniqueness `Mᵍ = M`.
  have hgM_mem : (MulAut.conj g • M) ∈
      maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    rw [mem_maximalSubgroupsContaining]
    refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul hMcoat, ?_⟩
    rw [← hgcent]
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff).mpr hCXM
  rw [hsing, Set.mem_singleton_iff] at hgM_mem
  -- `Mᵍ = M` gives `g ∈ N_G(M) = M`.
  have hgNM : g ∈ Subgroup.normalizer (M : Set G) :=
    OddOrder.GroupTheory.mem_normalizer_of_conj_smul_eq_self hgM_mem
  rwa [normalizer_eq_self_of_mem_maximalSubgroups hG (mem_maximalSubgroups.mpr hMcoat)] at hgNM

/-- **BG 14.7, swap argument — direction `⊆`** (mmd L3999): with `M` type-`P`, `K* = C_{M_σ}(K)`,
and a neighbour `Mi` containing `Z = K ⊔ K*` with `π(K*) ⊆ κ(Mi)`, for any line `X* ≤ K*` and any
Hall `κ(Mi)`-subgroup `Ki ∋ X*` (with `Ki* = C_{Mi_σ}(Ki)`),
`K ⊔ K* ≤ Ki ⊔ Ki*`.

`K`-part: `K` centralizes `K* ⊇ X*`, so `K ≤ N_G(X*)`, and `K ≤ Mi`; thus `K ≤ N_G(X*) ⊓ Mi =
Ki ⊔ Ki*` (Proposition 14.2(b1) for `Mi`).  `K*`-part (the "swap"): `K*` is a `κ(Mi)`-subgroup, so
it lies in *some* Hall `κ(Mi)`-subgroup `Ki' ⊇ K*`, and `N_G(X*) ⊓ Mi = Ki' ⊔ Ki'*` is the *same*
group as `Ki ⊔ Ki*` (it depends only on `X*`, not on the chosen Hall subgroup), so
`K* ≤ Ki' ≤ Ki ⊔ Ki*`. -/
theorem typeP_swap_Z_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mi Ki : Subgroup G}
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hZMi : K ⊔ Kstar ≤ Mi)
    (hKstarκ : ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi)
    {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXKstar : X ≤ Kstar)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi)) (hXKi : X ≤ Ki) :
    K ⊔ Kstar ≤ Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  set Kistar := OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) with hKistar
  -- `N_G(X) ⊓ Mi = Ki ⊔ Ki*` (Proposition 14.2(b1) for `Mi`, the reference choice of Hall subgroup).
  have hNeq : Subgroup.normalizer (X : Set G) ⊓ Mi = Ki ⊔ Kistar :=
    typeP_normalizer_inf_eq hG hMi hPi hKiMi hKi hp hX hXKi
  -- `K` centralizes `K*` (since `K* ≤ C_G(K)`), hence `K ≤ C_G(X) ≤ N_G(X)`.
  have hKCKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    have hKstarCK : Kstar ≤ Subgroup.centralizer (K : Set G) := hKstar ▸ inf_le_right
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hKstarCK hs) k hk).symm
  have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
    (hKCKstar.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXKstar))).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `K ≤ N_G(X) ⊓ Mi = Ki ⊔ Ki*`.
  have hKle : K ≤ Ki ⊔ Kistar := by
    rw [← hNeq]; exact le_inf hKNX (le_sup_left.trans hZMi)
  -- `K* ≤ Ki ⊔ Ki*` via the swap: pick a Hall `κ(Mi)`-subgroup `Ki' ⊇ K*`.
  have hKstarle : Kstar ≤ Ki ⊔ Kistar := by
    have hKstarMi : Kstar ≤ Mi := le_sup_right.trans hZMi
    obtain ⟨Ki', hKi'Mi, hKi', hKstarKi'⟩ :=
      exists_isHallSubgroup_kappa_ge hG hMi hKstarMi hKstarκ
    have hNeq' : Subgroup.normalizer (X : Set G) ⊓ Mi =
        Ki' ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki' : Set G)) :=
      typeP_normalizer_inf_eq hG hMi hPi hKi'Mi hKi' hp hX (hXKstar.trans hKstarKi')
    calc Kstar ≤ Ki' := hKstarKi'
      _ ≤ Ki' ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki' : Set G)) := le_sup_left
      _ = Subgroup.normalizer (X : Set G) ⊓ Mi := hNeq'.symm
      _ = Ki ⊔ Kistar := hNeq
  exact sup_le hKle hKstarle

/-- **BG 14.7, swap argument — the `Z`-coincidence** (mmd L3999-4001): the neighbour `Mi`'s own
direct-product decomposition coincides with `Z`, i.e. `Z = K ⊔ K* = Ki ⊔ Ki*`.

`M`/`K`/`K*` are the type-`P` data, `Mi` a nonconjugate type-`P` neighbour (e.g. the partner
`exists_typeP_partner` from a line `Xi ∈ ℰ¹(K)`) containing `Z` with `π(K*) ⊆ κ(Mi)`,
`Xi ⊆ Mi_σ`; `X* ∈ ℰ¹(K*)` is a line lying in a Hall `κ(Mi)`-subgroup `Ki`, with
`Ki* = C_{Mi_σ}(Ki)`.  Direction `⊆` is `typeP_swap_Z_le`.  Direction `⊇` re-runs the swap with
the roles of `(M, K, X*)` and `(Mi, Ki, Xi)` exchanged, using:
* `M ⊇ N_G(X*)` (`normalizer_le_of_maximalSubgroupsContaining_centralizer` applied to Prop 14.2(c)'s
  `ℳ(C_G(X*)) = {M}`), which gives `Ki ⊔ Ki* = N_G(X*) ⊓ Mi ≤ M`;
* `π(Ki*) ⊆ κ(M)` (`typeP_neighbor_kappa` for `Mi`, since `M` is the partner of `Mi` via `X*`);
* `Xi ⊆ Ki*` (`le_centralizerFactor_of_le_sup_of_le_Msigma`: `Xi`, a `σ(Mi)`-group inside
  `Ki × Ki*`, lands in the `σ`-factor `Ki*`). -/
theorem typeP_swap_Z_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mi Ki : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMimax : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hZMi : K ⊔ Kstar ≤ Mi)
    (hKstarκ : ∀ q ∈ (Nat.card ↥Kstar).primeFactors, q ∈ kappa Mi)
    {pstar : ℕ} (hpstar : pstar.Prime) {Xstar : Subgroup G}
    (hXstar : Xstar ∈ elemAbelianOfRank G pstar 1) (hXstarKstar : Xstar ≤ Kstar)
    (hXstarKi : Xstar ≤ Ki)
    {pi : ℕ} (hpi : pi.Prime) {Xi : Subgroup G}
    (hXi : Xi ∈ elemAbelianOfRank G pi 1) (hXiK : Xi ≤ K)
    (hXiMiσ : Xi ≤ OddOrder.BG.Ch3.S10.Msigma Mi)
    (hKiMi : Ki ≤ Mi) (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi)) :
    K ⊔ Kstar = Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
  classical
  haveI : Fact pstar.Prime := ⟨hpstar⟩
  -- Direction `⊆` (the original swap).
  have hle1 : K ⊔ Kstar ≤
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) :=
    typeP_swap_Z_le hG hKstar hMimax hPi hZMi hKstarκ hpstar hXstar hXstarKstar hKiMi hKi hXstarKi
  -- `ℳ(C_G(X*)) = {M}` (Prop 14.2(c)) and hence `N_G(X*) ≤ M`.
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hNXstarM : Subgroup.normalizer (Xstar : Set G) ≤ M :=
    normalizer_le_of_maximalSubgroupsContaining_centralizer hG
      (hc pstar hpstar Xstar hXstar hXstarKstar)
  -- `N_G(X*) ⊓ Mi = Ki ⊔ Ki*` (Prop 14.2(b1) for `Mi`).
  have hZiMi : Subgroup.normalizer (Xstar : Set G) ⊓ Mi =
      Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) :=
    typeP_normalizer_inf_eq hG hMimax hPi hKiMi hKi hpstar hXstar hXstarKi
  -- (A) `Ki ⊔ Ki* ≤ M`.
  have hA : Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ≤ M := by
    rw [← hZiMi]; exact inf_le_left.trans hNXstarM
  -- A Hall `(κ(Mi) ∪ σ(Mi))'`-subgroup of `Mi` (for Proposition 14.2 applied to `Mi`).
  haveI : IsSolvable ↥Mi := hG.solvable_of_mem_maximalSubgroups hMimax
  obtain ⟨Ui', hUi'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUieq : (Ui'.map Mi.subtype).subgroupOf Mi = Ui' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective Ui'
  have hUi : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((Ui'.map Mi.subtype).subgroupOf Mi) := by rw [hUieq]; exact hUi'
  -- (B) `π(Ki*) ⊆ κ(M)`: `M` is the partner of `Mi` via `X*` (`ℳ(N_G(X*)) = {M}`).
  have hKistarne : OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) ≠ ⊥ :=
    (typeP_structure hG hMimax hPi hKiMi hKi rfl hUi).2.1
  have hCXstarMi : OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Xstar : Set G) ≠ ⊥ :=
    fun hbot => hKistarne (le_bot_iff.mp (hbot ▸ inf_le_inf_left _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXstarKi))))
  have hM_in_NXstar : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (Xstar : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hNXstarM⟩
  have hB : ∀ q ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mi ⊓
      Subgroup.centralizer (Ki : Set G))).primeFactors, q ∈ kappa M :=
    typeP_neighbor_kappa hG hMimax hPi hKiMi hKi rfl hUi hXstar hXstarKi hCXstarMi hM_in_NXstar
  -- (C) `Xi ≤ Ki*` (`σ`-part extraction).
  have hXiCXstar : Xi ≤ Subgroup.centralizer (Xstar : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyCK : y ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.mem_inf.mp (hKstar ▸ hXstarKstar hy)).2
    exact (Subgroup.mem_centralizer_iff.mp hyCK a (hXiK ha)).symm
  have hXisup : Xi ≤ Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) := by
    rw [← hZiMi]
    exact le_inf (hXiCXstar.trans (Subgroup.centralizer_le_normalizer _))
      (hXiMiσ.trans (OddOrder.BG.Ch3.S10.Msigma_le Mi))
  have hKiMσbot : Ki ⊓ OddOrder.BG.Ch3.S10.Msigma Mi = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrKi hrMσ
    exact (kappaHall_isPiSubgroup_sigmaCompl hKiMi hKi r
        (Nat.mem_primeFactors.mpr ⟨hr, hrKi, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
  have hC : Xi ≤ OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) :=
    le_centralizerFactor_of_le_sup_of_le_Msigma inf_le_right inf_le_left hKiMσbot hXisup hXiMiσ
  -- Direction `⊇` (the swap with `(M, K, X*) ↔ (Mi, Ki, Xi)` exchanged).
  have hle2 : Ki ⊔ (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ≤
      K ⊔ Kstar := by
    have h := typeP_swap_Z_le hG (rfl :
      OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G) =
        OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G))
      hM hP hA hB hpi hXi hC hKM hK hXiK
    rwa [← hKstar] at h
  exact le_antisymm hle1 hle2

/-- **BG 14.7, Proposition 14.2(c) packaged** (the unique-centralizer clause): for a type-`P`
maximal `M` with Hall `κ(M)`-subgroup `K`, every line `Y ∈ ℰ¹(K*)` (`K* = C_{M_σ}(K)`) satisfies
`ℳ(C_G(Y)) = {M}`.  The Hall `(κ∪σ)'`-subgroup is produced internally, so callers supply only
`Y ≤ M_σ ⊓ C_G(K)`.  Used to show the `K_i*` are pairwise disjoint. -/
theorem typeP_centralizer_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    {p : ℕ} (hp : p.Prime) {Y : Subgroup G} (hY : Y ∈ elemAbelianOfRank G p 1)
    (hYK : Y ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  obtain ⟨_, _, _, _, _, hc, _⟩ := typeP_structure hG hM hP hKM hK rfl hU
  exact hc p hp Y hY hYK

/-- **BG 14.7, distinct neighbours have disjoint `K*`** (mmd L4005, "By Proposition 14.2(c)
applied to each `Mi`, `Ki* ∩ Kj* = 1` for `i ≠ j`"): if `Mi ≠ Mj` are type-`P` maximal
subgroups with Hall `κ`-subgroups `Ki`, `Kj`, then `C_{Mi_σ}(Ki) ⊓ C_{Mj_σ}(Kj) = ⊥`.

A common nonidentity element gives, by Cauchy, a line `Y ∈ ℰ¹(Ki* ⊓ Kj*)`; Proposition 14.2(c)
then forces `{Mi} = ℳ(C_G(Y)) = {Mj}`, i.e. `Mi = Mj`. -/
theorem typeP_neighbor_Kstar_inf_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mi Mj Ki Kj : Subgroup G}
    (hMi : Mi ∈ maximalSubgroups G) (hPi : IsTypeP Mi) (hKiMi : Ki ≤ Mi)
    (hKi : Ch03.IsHallSubgroup (kappa Mi) (Ki.subgroupOf Mi))
    (hMj : Mj ∈ maximalSubgroups G) (hPj : IsTypeP Mj) (hKjMj : Kj ≤ Mj)
    (hKj : Ch03.IsHallSubgroup (kappa Mj) (Kj.subgroupOf Mj))
    (hne : Mi ≠ Mj) :
    (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ⊓
      (OddOrder.BG.Ch3.S10.Msigma Mj ⊓ Subgroup.centralizer (Kj : Set G)) = ⊥ := by
  classical
  by_contra hbot
  set H := (OddOrder.BG.Ch3.S10.Msigma Mi ⊓ Subgroup.centralizer (Ki : Set G)) ⊓
    (OddOrder.BG.Ch3.S10.Msigma Mj ⊓ Subgroup.centralizer (Kj : Set G)) with hHdef
  -- Cauchy: a prime-order element `z ∈ H`, generating a line `Y ∈ ℰ¹(H)`.
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hbot
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥H)).ne'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hzH : (z : G) ∈ H := z.2
  have hzord : orderOf (z : G) = p := (orderOf_injective H.subtype H.subtype_injective z).trans hz
  have hYcard : Nat.card ↥(Subgroup.zpowers (z : G)) = p := by rw [Nat.card_zpowers, hzord]
  have hY : Subgroup.zpowers (z : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYH : Subgroup.zpowers (z : G) ≤ H := Subgroup.zpowers_le.mpr hzH
  -- `ℳ(C_G(Y)) = {Mi} = {Mj}`, so `Mi = Mj`, contradiction.
  have hi : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (z : G)) : Set G))
      = {Mi} := typeP_centralizer_singleton hG hMi hPi hKiMi hKi hp hY (hYH.trans inf_le_left)
  have hj : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (z : G)) : Set G))
      = {Mj} := typeP_centralizer_singleton hG hMj hPj hKjMj hKj hp hY (hYH.trans inf_le_right)
  exact hne (Set.singleton_eq_singleton_iff.mp (hi.symm.trans hj))

/-- **Inclusion–exclusion for subgroups meeting only at the identity** (BG 14.7 density backbone,
mmd L4031): for a nonempty finite family `{Sᵢ}_{i ∈ s}` of subgroups of `G` with `Sᵢ ⊓ Sⱼ = ⊥`
(`i ≠ j`), `|⋃ᵢ Sᵢ| + |s| = (∑ᵢ |Sᵢ|) + 1`.  Each `Sᵢ` contributes `|Sᵢ| − 1` non-identity
elements, all pairwise disjoint, plus the single shared identity.  In Theorem 14.7 (with `n + 1`
subgroups `Kᵢ*`) this gives `|T| = |Z| + n − ∑ kᵢ*` for `T = Z − ⋃ Kᵢ*`. -/
theorem ncard_biUnion_subgroup_add_card [Finite G] {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (S : ι → Subgroup G)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) :
    (⋃ i ∈ s, (S i : Set G)).ncard + s.card = (∑ i ∈ s, Nat.card ↥(S i)) + 1 := by
  classical
  have hcard_eq : ∀ i, (S i : Set G).ncard = Nat.card ↥(S i) := fun i =>
    (Nat.card_coe_set_eq (S i : Set G)).symm
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Finset.card_singleton,
      Finset.sum_singleton, hcard_eq]
  | cons a t ha htne ih =>
    have hpair_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → S i ⊓ S j = ⊥ := fun i hi j hj hij =>
      hpair i (Finset.mem_cons.mpr (Or.inr hi)) j (Finset.mem_cons.mpr (Or.inr hj)) hij
    have ih' := ih hpair_t
    -- `⋃_{cons a t} = S a ∪ ⋃_t`.
    have hunion : (⋃ i ∈ (Finset.cons a t ha), (S i : Set G))
        = (S a : Set G) ∪ ⋃ i ∈ t, (S i : Set G) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_cons, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨i, rfl | hi, hxi⟩
        · exact Or.inl hxi
        · exact Or.inr ⟨i, hi, hxi⟩
      · rintro (hxa | ⟨i, hi, hxi⟩)
        · exact ⟨a, Or.inl rfl, hxa⟩
        · exact ⟨i, Or.inr hi, hxi⟩
    -- `S a ∩ ⋃_t = {1}` (pairwise meet at the identity, `t` nonempty).
    have hinter : (S a : Set G) ∩ (⋃ i ∈ t, (S i : Set G)) = {1} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
      constructor
      · rintro ⟨hxa, i, hi, hxi⟩
        have hmem : x ∈ S a ⊓ S i := Subgroup.mem_inf.mpr ⟨hxa, hxi⟩
        rwa [hpair a (Finset.mem_cons_self a t) i (Finset.mem_cons.mpr (Or.inr hi))
          (fun h => ha (h ▸ hi)), Subgroup.mem_bot] at hmem
      · rintro rfl
        obtain ⟨i, hi⟩ := htne
        exact ⟨(S a).one_mem, i, hi, (S i).one_mem⟩
    have hunion_card : ((S a : Set G) ∪ ⋃ i ∈ t, (S i : Set G)).ncard + 1 =
        Nat.card ↥(S a) + (⋃ i ∈ t, (S i : Set G)).ncard := by
      have hfin1 : (S a : Set G).Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have hfin2 : (⋃ i ∈ t, (S i : Set G)).Finite :=
        Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      have h := Set.ncard_union_add_ncard_inter (S a : Set G) (⋃ i ∈ t, (S i : Set G)) hfin1 hfin2
      rw [hinter, Set.ncard_singleton, hcard_eq a] at h
      exact h
    rw [hunion, Finset.card_cons, Finset.sum_cons]
    omega

/-- **BG 14.7, the `T = Z − ⋃ Kᵢ*` density count** (mmd L4031): for a nonempty finite family
`{Sᵢ}_{i ∈ s}` of subgroups of `Z` pairwise meeting at `⊥`,
`|Z − ⋃ Sᵢ| + (∑ |Sᵢ|) + 1 = |Z| + |s|`, i.e. `|T| = |Z| + (|s| − 1) − ∑ |Sᵢ|`.
With `s.card = n + 1` this is BG's `|T| = z + n − ∑ kᵢ*`.  Combines the inclusion–exclusion
count with the complement `|Z − ⋃| + |⋃| = |Z|`. -/
theorem ncard_sdiff_biUnion_subgroup [Finite G] {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (S : ι → Subgroup G) {Z : Subgroup G} (hSZ : ∀ i ∈ s, S i ≤ Z)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S i ⊓ S j = ⊥) :
    ((Z : Set G) \ ⋃ i ∈ s, (S i : Set G)).ncard + (∑ i ∈ s, Nat.card ↥(S i)) + 1
      = Nat.card ↥Z + s.card := by
  classical
  have hsub : (⋃ i ∈ s, (S i : Set G)) ⊆ (Z : Set G) :=
    Set.iUnion₂_subset (fun i hi => SetLike.coe_subset_coe.mpr (hSZ i hi))
  have hIE := ncard_biUnion_subgroup_add_card hs S hpair
  have hdiff := Set.ncard_diff_add_ncard_of_subset hsub
  have hZcard : Nat.card ↥Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
  omega

/-- **Internal direct product cardinality** (BG 14.7 `z = ∏ kᵢ*`, mmd L4009): a finite family
`{Hᵢ}` of pairwise-commuting subgroups with pairwise-coprime orders is an internal direct product,
so `|⨆ᵢ Hᵢ| = ∏ᵢ |Hᵢ|`.  (Independence comes from coprimality via
`Subgroup.independent_of_coprime_order`; the `noncommPiCoprod` map is then injective with range
`⨆ Hᵢ`.)  In Theorem 14.7, applied to the `Kᵢ*` (Hall `σ(Mᵢ)`-subgroups of `Z`, pairwise coprime
since the `σ(Mᵢ)` are disjoint) it gives `z = ∏ kᵢ*` and hence `kᵢ = ∏_{j≠i} kⱼ*`. -/
theorem card_iSup_of_pairwise_commute_coprime [Finite G] {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card ↥(H i)) (Nat.card ↥(H j))) :
    Nat.card ↥(⨆ i, H i) = ∏ i, Nat.card ↥(H i) := by
  classical
  haveI : ∀ i, Fintype ↥(H i) := fun i => Fintype.ofFinite _
  have hcop' : Pairwise fun i j => Nat.Coprime (Fintype.card ↥(H i)) (Fintype.card ↥(H j)) :=
    fun i j hij => by simpa only [Nat.card_eq_fintype_card] using hcoprime hij
  have hind : iSupIndep H := Subgroup.independent_of_coprime_order hcomm hcop'
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hrange : (Subgroup.noncommPiCoprod hcomm).range = ⨆ i, H i :=
    Subgroup.noncommPiCoprod_range
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_pi]

/-- **BG 14.7, the canonical form of `Kᵢ*`** (mmd L4009): once the swap gives `Z = Kₙ ⊔ Kₙ*`
(`Kₙ* = C_{Nσ}(Kₙ)`), the factor `Kₙ*` is exactly `Z ⊓ Nσ` — the `σ(N)`-part of `Z`.  This
removes the dependence of `Kₙ*` on the chosen Hall `κ(N)`-subgroup `Kₙ`: it is the canonical
`Z ⊓ M_σ(N)`, so the family `{Kᵢ*}` can be defined choice-free as `N ↦ Z ⊓ Nσ`.

`⊆`: `Kₙ* ≤ Z` (a factor) and `Kₙ* ≤ Nσ`.  `⊇`: `Z ⊓ Nσ = (Kₙ ⊔ Kₙ*) ⊓ Nσ` is a `σ(N)`-group
inside the product `Kₙ × Kₙ*`, so the `σ`-projection lands it in `Kₙ*`. -/
theorem typeP_neighbor_Kstar_eq_Z_inf_Msigma [Finite G]
    {N K Kstar KN : Subgroup G} (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hZeq : K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))) :
    OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
      = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  classical
  refine le_antisymm (le_inf (hZeq ▸ le_sup_right) inf_le_left) ?_
  rw [hZeq]
  have hKNMσbot : KN ⊓ OddOrder.BG.Ch3.S10.Msigma N = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrKN hrMσ
    exact (kappaHall_isPiSubgroup_sigmaCompl hKNN hKN r
        (Nat.mem_primeFactors.mpr ⟨hr, hrKN, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N r
        (Nat.mem_primeFactors.mpr ⟨hr, hrMσ, Nat.card_pos.ne'⟩))
  exact le_centralizerFactor_of_le_sup_of_le_Msigma inf_le_right inf_le_left hKNMσbot
    inf_le_left inf_le_right

/-- **Base member of the type-`P` family**: `Z ⊓ M_σ = K*` for `M` itself.  Specialises
`typeP_neighbor_Kstar_eq_Z_inf_Msigma` to `N = M`, `K_N = K` (so `K* = M_σ ⊓ C(K)` is the
canonical `σ(M)`-part of `Z = K ⊔ K*`).  This is the base case of the `T = Ẑ` identification:
the exceptional set `T = Z ∖ ⋃_{N} (Z ⊓ N_σ)` removes `K*` (from `N = M`) and `K` (from the
partner), collapsing to `zTilde K K* = Z ∖ (K ∪ K*)`. -/
theorem typeP_Z_inf_Msigma_eq_Kstar [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar := by
  have h := typeP_neighbor_Kstar_eq_Z_inf_Msigma (N := M) (KN := K) (K := K) (Kstar := Kstar)
    hKM hK (by rw [hKstar])
  rw [← h, ← hKstar]

/-- **BG 14.7, per-neighbour swap package** (mmd L3997-4009): for a type-`P` maximal `M` with Hall
data `K`, `K*`, a line `X ∈ ℰ_p¹(K)` (`C_{M_σ}(X) ≠ 1`) and a maximal `N ⊇ N_G(X)`, there is a
Hall `κ(N)`-subgroup `K_N` of `N` realising the swap: `Z = K ⊔ K* = K_N ⊔ K_N*` with the canonical
factor `K_N* = Z ⊓ M_σ(N)`.  This is the per-neighbour foundation that the `M_i` family iterates
over: assembles `typeP_neighbor_embed`/`typeP_neighbor_kappa` (neighbour data), a chosen line
`X* ∈ ℰ¹(K*)` with a Hall `κ(N)`-subgroup `K_N ∋ X*`, `typeP_swap_Z_eq` (the swap) and
`typeP_neighbor_Kstar_eq_Z_inf_Msigma` (the canonical form). -/
theorem exists_neighbor_kappaHall_swap [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  classical
  obtain ⟨hnc, hZN, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hNmax : N ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hN).1
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hqκN : q ∈ kappa N := hκ q hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
  -- A line `X* ∈ ℰ¹(K*)` of prime order `q`, inside a Hall `κ(N)`-subgroup `K_N`.
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' q (Nat.dvd_of_mem_primeFactors hq)
  have hx'ord : orderOf (x' : G) = q :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x').trans hx'
  have hXstarcard : Nat.card ↥(Subgroup.zpowers (x' : G)) = q := by rw [Nat.card_zpowers, hx'ord]
  have hXstarElem : Subgroup.zpowers (x' : G) ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXstarcard, by rw [hXstarcard, pow_one]⟩
  have hXstarKstar : Subgroup.zpowers (x' : G) ≤ Kstar := Subgroup.zpowers_le.mpr x'.2
  have hXstarκN : ∀ r ∈ (Nat.card ↥(Subgroup.zpowers (x' : G))).primeFactors, r ∈ kappa N := by
    intro r hr
    rw [hXstarcard, (Nat.prime_of_mem_primeFactors hq).primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hqκN
  obtain ⟨KN, hKNN, hKN, hXstarKN⟩ :=
    exists_isHallSubgroup_kappa_ge hG hNmax (hXstarKstar.trans (le_sup_right.trans hZN)) hXstarκN
  have hswap : K ⊔ Kstar =
      KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) :=
    typeP_swap_Z_eq hG hM hP hKM hK hKstar hU hNmax ⟨q, hqκN⟩ hZN hκ
      (Nat.prime_of_mem_primeFactors hq) hXstarElem hXstarKstar hXstarKN
      Fact.out hX hXK hXNσ hKNN hKN
  exact ⟨KN, hKNN, hKN, hswap, typeP_neighbor_Kstar_eq_Z_inf_Msigma hKNN hKN hswap⟩

/-- **BG 14.7, coverage of `κ(M)`-primes** (mmd L4007): every prime `p ∣ |K|` lies in `σ(N)` for
some nonconjugate type-`P` neighbour `N` containing `Z`.  A line `X ∈ ℰ_p¹(K)` (Cauchy in `K`) has
a partner `N ∈ 𝓜(N_G(X))` (`exists_typeP_partner`) with `X ⊆ M_σ(N)`, so `p ∈ σ(N)`.  Together with
`M` itself (covering `σ(M) ⊇ π(K*)`), this gives the coverage `⋃ σ(Mᵢ) ⊇ π(Z)` that forces
`⨆ Kᵢ* = Z`. -/
theorem exists_typeP_neighbor_mem_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ IsTypeP N ∧ ¬ IsConjugateSubgroup M N ∧
      p ∈ OddOrder.BG.Ch3.S10.sigma N ∧ K ⊔ Kstar ≤ N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, hZN, hXNσ, _, hPN⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNmax : N ∈ maximalSubgroups G :=
    mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hNmem).1
  -- `p ∈ σ(N)` since `X ⊆ M_σ(N)` and `p ∣ |X|`.
  have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hp, (by rw [hXcard] : p ∣ Nat.card ↥(Subgroup.zpowers (x : G))).trans
        (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)
  exact ⟨N, hNmax, hPN, hnc, hpσN, hZN⟩

/-- **Both factors of an internal direct product are normal**: in `A ⊔ B` with `B ≤ C_G(A)`
(so `A`, `B` commute), `A ⊔ B ≤ N_G(A) ⊓ N_G(B)`.  In Theorem 14.7, applied to the swap
`Z = K_N ⊔ K_N*` (`K_N* ≤ C(K_N)`), it makes both `K_N` and `K_N* = Z ⊓ M_σ(N)` normal in `Z` —
the input to pairwise commutativity of the `Kᵢ*` (for `z = ∏ kᵢ*`), to pairwise nonconjugacy of
the `Mᵢ`, and to the `n = 1` collapse (`Kᵢ ◁ Z` is the unique `σ(Mᵢ)'`-Hall). -/
theorem sup_le_normalizer_inf_of_commute {A B : Subgroup G}
    (h : B ≤ Subgroup.centralizer (A : Set G)) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) := by
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (Subgroup.mem_centralizer_iff.mp (h hb) a ha).symm
  exact le_inf
    (sup_le Subgroup.le_normalizer (h.trans (Subgroup.centralizer_le_normalizer _)))
    (sup_le (hAB.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)

/-- **Internal direct product of two commuting subgroups**: if `H`, `K` commute elementwise and
`H ⊓ K = ⊥`, then `|H ⊔ K| = |H|·|K|`.  (The `noncommCoprod` map `↥H × ↥K → ↥(H ⊔ K)` is an
isomorphism.)  Used by the family argument for `|Kᵢ* ⊔ Kⱼ*| = kᵢ*·kⱼ*` (pairwise nonconjugacy) and
in the `n = 1` collapse. -/
theorem card_sup_of_commute_of_disjoint [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, Commute x y) (hdisj : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have hc : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hcomm (a : G) a.2 (b : G) b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hc) :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr
      ⟨H.subtype_injective, K.subtype_injective, by
        rw [H.range_subtype, K.range_subtype]; exact disjoint_iff.mpr hdisj⟩
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hc).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, H.range_subtype, K.range_subtype]
  rw [← Nat.card_congr
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).toEquiv, Nat.card_prod]

/-- **Subgroups normal in a common overgroup, meeting trivially, commute**: if `A, B ≤ Z` with
`Z ≤ N_G(A)`, `Z ≤ N_G(B)` (so `A, B ◁ Z`) and `A ⊓ B = ⊥`, then every element of `A` commutes with
every element of `B`.  (The commutator `[x,y]` lies in `A ⊓ B = ⊥`.)  Used for `|Kᵢ* ⊔ Kⱼ*| =
kᵢ*·kⱼ*` once the `Kᵢ*` are known normal in `Z`. -/
theorem commute_of_le_normalizer_of_disjoint {Z A B : Subgroup G}
    (hAZ : A ≤ Z) (hBZ : B ≤ Z) (hAnorm : Z ≤ Subgroup.normalizer (A : Set G))
    (hBnorm : Z ≤ Subgroup.normalizer (B : Set G)) (hdisj : A ⊓ B = ⊥) :
    ∀ x ∈ A, ∀ y ∈ B, Commute x y := by
  haveI hAn : (A.subgroupOf Z).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAnorm
  haveI hBn : (B.subgroupOf Z).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBnorm
  have hdisjZ : Disjoint (A.subgroupOf Z) (B.subgroupOf Z) := by
    rw [Subgroup.disjoint_def]
    intro g hgA hgB
    have : (g : G) ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hgA, Subgroup.mem_subgroupOf.mp hgB⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact OneMemClass.coe_eq_one.mp this
  intro x hx y hy
  have h := Subgroup.commute_of_normal_of_disjoint (A.subgroupOf Z) (B.subgroupOf Z) hAn hBn hdisjZ
    ⟨x, hAZ hx⟩ ⟨y, hBZ hy⟩ (Subgroup.mem_subgroupOf.mpr hx) (Subgroup.mem_subgroupOf.mpr hy)
  exact h.map Z.subtype

/-- **BG 14.7, pairwise nonconjugacy of the family** (mmd L4015, "the `Mᵢ` are pairwise not
conjugate"): if `M₁`, `M₂` are maximal subgroups whose swap factors `Zₖ = M_σ(Mₖ) ⊓ C(Kₖ)` (the
`σ(Mₖ)`-Halls of `Z = K ⊔ K*`, `Kₖ` Hall `κ(Mₖ)`) meet trivially and `Z₂ ≠ ⊥`, then `M₁`, `M₂` are
nonconjugate.

Were they conjugate, `σ(M₁) = σ(M₂) =: τ`, so `Z₁`, `Z₂` are both `τ`-Halls of `Z`, normal
(direct factors) and disjoint.  Then `|Z₁ ⊔ Z₂| = z₁ z₂ ∣ z = k₁ z₁`, giving `z₂ ∣ k₁`; but `z₂` is
a `τ`-number and `k₁` a `τ'`-number, so `z₂ = 1`, contradicting `Z₂ ≠ ⊥`.  Feeds Lemma 14.5(b)
(pairwise disjointness of the `𝒞_G(M̃ᵢ)`). -/
theorem typeP_family_nonconjugate [Finite G]
    {K Kstar M₁ M₂ K₁ K₂ : Subgroup G}
    (hK₁M₁ : K₁ ≤ M₁) (hK₁ : Ch03.IsHallSubgroup (kappa M₁) (K₁.subgroupOf M₁))
    (hsw₁ : K ⊔ Kstar = K₁ ⊔ (OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G)))
    (hsw₂ : K ⊔ Kstar = K₂ ⊔ (OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G)))
    (hne₂ : OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥)
    (hdisj : (OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G)) ⊓
      (OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G)) = ⊥) :
    ¬ IsConjugateSubgroup M₁ M₂ := by
  classical
  set Z₁ := OddOrder.BG.Ch3.S10.Msigma M₁ ⊓ Subgroup.centralizer (K₁ : Set G) with hZ₁def
  set Z₂ := OddOrder.BG.Ch3.S10.Msigma M₂ ⊓ Subgroup.centralizer (K₂ : Set G) with hZ₂def
  rintro ⟨g, hg⟩
  have hσ : OddOrder.BG.Ch3.S10.sigma M₂ = OddOrder.BG.Ch3.S10.sigma M₁ := by
    rw [← hg]; exact sigma_conj_smul_eq g M₁
  have hZ₁CK₁ : Z₁ ≤ Subgroup.centralizer (K₁ : Set G) := by rw [hZ₁def]; exact inf_le_right
  have hZ₁Mσ : Z₁ ≤ OddOrder.BG.Ch3.S10.Msigma M₁ := by rw [hZ₁def]; exact inf_le_left
  have hZ₂CK₂ : Z₂ ≤ Subgroup.centralizer (K₂ : Set G) := by rw [hZ₂def]; exact inf_le_right
  have hZ₂Mσ : Z₂ ≤ OddOrder.BG.Ch3.S10.Msigma M₂ := by rw [hZ₂def]; exact inf_le_left
  have hcommK₁Z₁ : ∀ x ∈ K₁, ∀ y ∈ Z₁, Commute x y := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hZ₁CK₁ hy) x hx
  have hdisjK₁Z₁ : K₁ ⊓ Z₁ = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hrK₁ hrZ₁
    exact kappaHall_isPiSubgroup_sigmaCompl hK₁M₁ hK₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hrK₁, Nat.card_pos.ne'⟩)
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₁ r (Nat.mem_primeFactors.mpr
        ⟨hr, hrZ₁.trans (Subgroup.card_dvd_of_le hZ₁Mσ), Nat.card_pos.ne'⟩))
  have hzcard : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K₁ * Nat.card ↥Z₁ := by
    rw [hsw₁]; exact card_sup_of_commute_of_disjoint hcommK₁Z₁ hdisjK₁Z₁
  have hZ₁Z : Z₁ ≤ K ⊔ Kstar := by rw [hsw₁]; exact le_sup_right
  have hZ₂Z : Z₂ ≤ K ⊔ Kstar := by rw [hsw₂]; exact le_sup_right
  have hZ₁norm : K ⊔ Kstar ≤ Subgroup.normalizer (Z₁ : Set G) := by
    rw [hsw₁]; exact (sup_le_normalizer_inf_of_commute hZ₁CK₁).trans inf_le_right
  have hZ₂norm : K ⊔ Kstar ≤ Subgroup.normalizer (Z₂ : Set G) := by
    rw [hsw₂]; exact (sup_le_normalizer_inf_of_commute hZ₂CK₂).trans inf_le_right
  have hz12 : Nat.card ↥(Z₁ ⊔ Z₂) = Nat.card ↥Z₁ * Nat.card ↥Z₂ :=
    card_sup_of_commute_of_disjoint
      (commute_of_le_normalizer_of_disjoint hZ₁Z hZ₂Z hZ₁norm hZ₂norm hdisj) hdisj
  have hdvd : Nat.card ↥(Z₁ ⊔ Z₂) ∣ Nat.card ↥(K ⊔ Kstar) :=
    Subgroup.card_dvd_of_le (sup_le hZ₁Z hZ₂Z)
  rw [hz12, hzcard] at hdvd
  have hZ₂dvdK₁ : Nat.card ↥Z₂ ∣ Nat.card ↥K₁ := by
    rw [mul_comm (Nat.card ↥K₁)] at hdvd
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hdvd
  have hcop : Nat.Coprime (Nat.card ↥Z₂) (Nat.card ↥K₁) :=
    coprime_of_forall_prime_not_dvd (fun r hr hrZ₂ hrK₁ =>
      kappaHall_isPiSubgroup_sigmaCompl hK₁M₁ hK₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hrK₁, Nat.card_pos.ne'⟩)
        (hσ ▸ OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ r (Nat.mem_primeFactors.mpr
          ⟨hr, hrZ₂.trans (Subgroup.card_dvd_of_le hZ₂Mσ), Nat.card_pos.ne'⟩)))
  have hZ₂one : Nat.card ↥Z₂ = 1 := (Nat.gcd_eq_left hZ₂dvdK₁).symm.trans hcop
  exact hne₂ (Subgroup.card_eq_one.mp hZ₂one)

/-- **BG 14.7, per-neighbour swap package with normality** (mmd L3997-4015): the per-neighbour
swap `exists_neighbor_kappaHall_swap`, restated with the canonical factor `K_N* = Z ⊓ M_σ(N)`
folded into the swap and augmented with `K_N* ◁ Z` (`Z ≤ N_G(K_N*)`).  This is the exact per-member
data the `M_i` family consumes: the swap `Z = K_N ⊔ K_N*`, the canonical `K_N*`, and its normality
in `Z` (for pairwise commutativity, the `|T|` count, and the `n = 1` collapse). -/
theorem exists_neighbor_kappaHall_swap_normal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      K ⊔ Kstar ≤ Subgroup.normalizer
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  obtain ⟨KN, hKNN, hKN, hswap, hcanon⟩ :=
    exists_neighbor_kappaHall_swap hG hM hP hKM hK hKstar hU hX hXK hCX hN
  refine ⟨KN, hKNN, hKN, hswap.trans (by rw [hcanon]), ?_⟩
  rw [← hcanon, hswap]
  exact (sup_le_normalizer_inf_of_commute inf_le_right).trans inf_le_right

/-- **BG 14.7, full per-neighbour data** (mmd L3997-4015): the complete per-member package the
`M_i` family consumes — for a line `X ∈ ℰ_p¹(K)` and a maximal `N ⊇ N_G(X)`, a Hall `κ(N)`-subgroup
`K_N` with the swap `Z = K_N ⊔ K_N*` (canonical `K_N* = Z ⊓ M_σ(N)`), `K_N* ◁ Z`, `N` type-`P`, and
`K_N* ≠ ⊥` (since `X ≤ K_N*`, as `X ≤ K ≤ Z` and `X ⊆ M_σ(N)`).  Builds on
`exists_neighbor_kappaHall_swap_normal` + `typeP_neighbor_embed`/`typeP_neighbor_kappa`. -/
theorem exists_neighbor_full [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      K ⊔ Kstar ≤ Subgroup.normalizer
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) ∧
      IsTypeP N ∧ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := by
  obtain ⟨KN, hKNN, hKN, hswap, hnorm⟩ :=
    exists_neighbor_kappaHall_swap_normal hG hM hP hKM hK hKstar hU hX hXK hCX hN
  obtain ⟨_, _, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hPN : IsTypeP N := ⟨q, hκ q hq⟩
  have hXKstar : X ≤ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    le_inf (hXK.trans le_sup_left) hXNσ
  have hKstarNne : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := fun hbot =>
    ne_bot_of_mem_elemAbelianOfRank_one hX (le_bot_iff.mp (hbot ▸ hXKstar))
  exact ⟨KN, hKNN, hKN, hswap, hnorm, hPN, hKstarNne⟩

/-- **BG 14.7, two family members are nonconjugate** (mmd L4015): given two type-`P` maximals
`N₁ ≠ N₂` with Hall `κ`-subgroups and the swaps `Z = Kₖ ⊔ (M_σ(Nₖ) ⊓ C(Kₖ))` (`Z₂* ≠ ⊥`), the
members are nonconjugate.  Combines Proposition 14.2(c) (`typeP_neighbor_Kstar_inf_eq_bot`: the swap
factors meet trivially since the members are distinct) with `typeP_family_nonconjugate`.  This is
the per-pair input to the family's pairwise nonconjugacy (and thence Lemma 14.5(b)). -/
theorem neighbor_pair_nonconjugate [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {K Kstar N₁ N₂ K₁ K₂ : Subgroup G}
    (hN₁ : N₁ ∈ maximalSubgroups G) (hP₁ : IsTypeP N₁) (hK₁N₁ : K₁ ≤ N₁)
    (hK₁ : Ch03.IsHallSubgroup (kappa N₁) (K₁.subgroupOf N₁))
    (hN₂ : N₂ ∈ maximalSubgroups G) (hP₂ : IsTypeP N₂) (hK₂N₂ : K₂ ≤ N₂)
    (hK₂ : Ch03.IsHallSubgroup (kappa N₂) (K₂.subgroupOf N₂))
    (hsw₁ : K ⊔ Kstar = K₁ ⊔ (OddOrder.BG.Ch3.S10.Msigma N₁ ⊓ Subgroup.centralizer (K₁ : Set G)))
    (hsw₂ : K ⊔ Kstar = K₂ ⊔ (OddOrder.BG.Ch3.S10.Msigma N₂ ⊓ Subgroup.centralizer (K₂ : Set G)))
    (hne₂ : OddOrder.BG.Ch3.S10.Msigma N₂ ⊓ Subgroup.centralizer (K₂ : Set G) ≠ ⊥)
    (hne : N₁ ≠ N₂) :
    ¬ IsConjugateSubgroup N₁ N₂ :=
  typeP_family_nonconjugate hK₁N₁ hK₁ hsw₁ hsw₂ hne₂
    (typeP_neighbor_Kstar_inf_eq_bot hG hN₁ hP₁ hK₁N₁ hK₁ hN₂ hP₂ hK₂N₂ hK₂ hne)

/-- **BG 14.7, the base member `M` (`i = 0`)** (mmd L4003, "let `M₀ = M`"): `M`'s own data in the
same canonical shape the family uses.  `K_M* = Z ⊓ M_σ(M)` equals `K* = Kstar`, the swap
`Z = K ⊔ K_M*` is trivial, `K_M* ◁ Z`, and `K_M* ≠ ⊥` (since `Kstar ≠ ⊥`).  Aligns `M` with the
neighbours (`exists_neighbor_full`) so the family `{M} ∪ {neighbours}` has uniform per-member data. -/
theorem typeP_self_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar ∧
    K ⊔ Kstar = K ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M) ∧
    K ⊔ Kstar ≤ Subgroup.normalizer
      (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ := by
  have hcanon : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M :=
    typeP_neighbor_Kstar_eq_Z_inf_Msigma hKM hK (by rw [hKstar])
  have hKstarEq : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar := hcanon.symm.trans hKstar.symm
  refine ⟨hKstarEq, by rw [hKstarEq], ?_, ?_⟩
  · rw [hKstarEq, hKstar]
    exact (sup_le_normalizer_inf_of_commute inf_le_right).trans inf_le_right
  · rw [hKstarEq]; exact (typeP_structure hG hM hP hKM hK hKstar hU).2.1

/-- **A subgroup of order coprime to a normal subgroup's index lies inside it** (BG 14.7 `n = 1`
collapse, mmd L4043): if `N ◁ G` and `|H|` is coprime to `[G : N]`, then `H ≤ N`.  (The image of
`H` in `G/N` has order dividing both `|H|` and `[G : N]`, hence `1`, so `H ≤ ker = N`.)  In the
collapse, applied with `N = Kᵢ` (the normal `σ(Mᵢ)'`-Hall of `Z`, `[Z : Kᵢ] = kᵢ*` a `σ(Mᵢ)`-number)
and `H = Kⱼ*` (a `σ(Mᵢ)'`-group), it gives `Kⱼ* ≤ Kᵢ`; with `|Kᵢ|` prime this forces `Kⱼ* = Kᵢ`. -/
theorem le_of_coprime_index {N H : Subgroup G} [N.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) N.index) : H ≤ N := by
  have hd1 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ Nat.card ↥H :=
    Subgroup.card_map_dvd H (QuotientGroup.mk' N)
  have hd2 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ∣ N.index :=
    Subgroup.card_subgroup_dvd_card _
  have hcard1 : Nat.card ↥(H.map (QuotientGroup.mk' N)) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hbot : H.map (QuotientGroup.mk' N) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard1
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

/-- **BG 14.7, unified per-neighbour data** (mmd L3997-4015): the single per-member source for the
family, exposing the **raw** swap factor `K_N* = M_σ(N) ⊓ C(K_N)` (for pairwise nonconjugacy and the
`z = k_N·k_N*` card) together with the **canonical identity** `K_N* = Z ⊓ M_σ(N)` (for the family's
`Kᵢ*`), plus `N` type-`P` and `K_N* ≠ ⊥`.  Resolves the raw/canonical form tension at the source. -/
theorem exists_neighbor_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXK : X ≤ K)
    (hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥)
    {N : Subgroup G} (hN : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ∧
      IsTypeP N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G) ≠ ⊥ := by
  obtain ⟨KN, hKNN, hKN, hswap, hcanon⟩ :=
    exists_neighbor_kappaHall_swap hG hM hP hKM hK hKstar hU hX hXK hCX hN
  obtain ⟨_, _, hXNσ⟩ := typeP_neighbor_embed hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hκ := typeP_neighbor_kappa hG hM hP hKM hK hKstar hU hX hXK hCX hN
  have hKstarne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  haveI : Nontrivial ↥Kstar := (Subgroup.nontrivial_iff_ne_bot _).mpr hKstarne
  obtain ⟨q, hq⟩ : (Nat.card ↥Kstar).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hXcanon : X ≤ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    le_inf (hXK.trans le_sup_left) hXNσ
  exact ⟨KN, hKNN, hKN, hswap, hcanon, ⟨q, hκ q hq⟩, fun hbot =>
    ne_bot_of_mem_elemAbelianOfRank_one hX (le_bot_iff.mp (hbot ▸ hcanon.symm ▸ hXcanon))⟩

/-- **BG 14.7, the family member predicate** (mmd L4003): `N` is a member of the type-`P` family
attached to `Z` — either `N = M`, or `N` is a maximal subgroup over `N_G(X)` for a line
`X ∈ ℰ_p¹(K)`. -/
def IsZFamilyMember (M K N : Subgroup G) : Prop :=
  N = M ∨ ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ X ∈ elemAbelianOfRank G p 1 ∧ X ≤ K ∧
    N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G))

/-- **BG 14.7, uniform per-member data for the family** (mmd L4003-4015): every member `N` of the
type-`P` family is a type-`P` maximal subgroup containing `Z = K ⊔ K*`, with a Hall `κ(N)`-subgroup
`K_N` realising the swap `Z = K_N ⊔ K_N*` (raw `K_N* = M_σ(N) ⊓ C(K_N)`, canonical
`K_N* = Z ⊓ M_σ(N)`, `K_N* ≠ ⊥`).  Case-split on `N = M` (`typeP_self_member`) vs a neighbour
(`exists_neighbor_data`); this is the data the family `Finset` carries. -/
theorem typeP_family_member_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    N ∈ maximalSubgroups G ∧ IsTypeP N ∧ K ⊔ Kstar ≤ N ∧
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G) ≠ ⊥ := by
  rcases hN with hNM | ⟨p, X, hp, hX, hXK, hN⟩
  · -- `N = M`: base member.
    rw [hNM]
    obtain ⟨hKstarEq, _, _, _⟩ := typeP_self_member hG hM hP hKM hK hKstar hU
    refine ⟨hM, hP, sup_le hKM (hKstar ▸ inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)),
      K, hKM, hK, by rw [hKstar], (hKstarEq.trans hKstar).symm,
      hKstar ▸ (typeP_structure hG hM hP hKM hK hKstar hU).2.1⟩
  · -- neighbour from a line `X`.
    haveI : Fact p.Prime := ⟨hp⟩
    have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      refine (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (le_bot_iff.mp ?_)
      rw [hKstar]
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
          ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
        _ = ⊥ := hbot
    obtain ⟨KN, hKNN, hKN, hswap, hcanon, hPN, hne⟩ :=
      exists_neighbor_data hG hM hP hKM hK hKstar hU hX hXK hCX hN
    refine ⟨mem_maximalSubgroups.mpr (mem_maximalSubgroupsContaining.mp hN).1, hPN,
      hswap ▸ sup_le hKNN (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le N)),
      KN, hKNN, hKN, hswap, hcanon, hne⟩

/-- **BG 14.7, the family is pairwise nonconjugate** (mmd L4015): any two distinct members of the
type-`P` family are nonconjugate.  Extracts each member's swap data
(`typeP_family_member_data`) and applies `neighbor_pair_nonconjugate`.  Feeds Lemma 14.5(b)
(pairwise disjointness of the `𝒞_G(M̃ᵢ)`). -/
theorem typeP_family_pairwise_nonconjugate [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ¬ IsConjugateSubgroup N₁ N₂ := by
  obtain ⟨hN₁max, hP₁, _, K₁, hK₁N₁, hK₁, hsw₁, _, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, hP₂, _, K₂, hK₂N₂, hK₂, hsw₂, _, hne₂⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  exact neighbor_pair_nonconjugate hG hN₁max hP₁ hK₁N₁ hK₁ hN₂max hP₂ hK₂N₂ hK₂ hsw₁ hsw₂ hne₂ hne

/-- **BG 14.7, the family `Kᵢ*` are pairwise disjoint** (mmd L4005): for distinct members
`N₁ ≠ N₂`, the canonical factors `Kᵢ* = Z ⊓ M_σ(Nᵢ)` meet trivially.  Distinct members are
nonconjugate (`typeP_family_pairwise_nonconjugate`), so `σ(N₁)`, `σ(N₂)` are disjoint
(Theorem 13.9), hence `M_σ(N₁) ⊓ M_σ(N₂) = ⊥` (coprime `σ`-groups), and a fortiori the `Kᵢ*` meet
trivially.  This is the pairwise-`⊥` input to the inclusion–exclusion `|T|` count. -/
theorem typeP_family_Kstar_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁) ⊓
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂) = ⊥ := by
  obtain ⟨hN₁max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  have hnc := typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU hN₁ hN₂ hne
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₁max hN₂max hnc
  have hMσdisj : OddOrder.BG.Ch3.S10.Msigma N₁ ⊓ OddOrder.BG.Ch3.S10.Msigma N₂ = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime (coprime_of_forall_prime_not_dvd ?_)
    intro r hr hr₁ hr₂
    exact Set.disjoint_left.mp hσdisj
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₁ r
        (Nat.mem_primeFactors.mpr ⟨hr, hr₁, Nat.card_pos.ne'⟩))
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₂ r
        (Nat.mem_primeFactors.mpr ⟨hr, hr₂, Nat.card_pos.ne'⟩))
  exact le_bot_iff.mp (le_trans (inf_le_inf inf_le_right inf_le_right) (le_of_eq hMσdisj))

/-- **BG 14.7, the family `Kᵢ*` have pairwise coprime order** (mmd L4009): for distinct members
`N₁ ≠ N₂`, `|Kᵢ*| = |Z ⊓ M_σ(Nᵢ)|` are coprime — each `Kᵢ*` is a `σ(Nᵢ)`-group and the `σ(Nᵢ)` are
pairwise disjoint (Theorem 13.9 via `typeP_family_pairwise_nonconjugate`).  This is the
coprime-orders input to `card_iSup_of_pairwise_commute_coprime` for `z = ∏ kᵢ*`. -/
theorem typeP_family_Kstar_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    Nat.Coprime (Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁))
      (Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂)) := by
  obtain ⟨hN₁max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₁
  obtain ⟨hN₂max, _, _, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN₂
  have hnc := typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU hN₁ hN₂ hne
  have hσdisj := OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₁max hN₂max hnc
  refine coprime_of_forall_prime_not_dvd ?_
  intro r hr hr₁ hr₂
  exact Set.disjoint_left.mp hσdisj
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₁ r
      (Nat.mem_primeFactors.mpr
        ⟨hr, hr₁.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩))
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₂ r
      (Nat.mem_primeFactors.mpr
        ⟨hr, hr₂.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩))

/-- **BG 14.7, the type-`P` family as a `Finset`** (mmd L4003): `{N | IsZFamilyMember M K N}`
collected as a `Finset` (finite since `Subgroup G` is finite). -/
noncomputable def ZFamilyFinset [Finite G] (M K : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite {N | IsZFamilyMember M K N}).toFinset

theorem mem_ZFamilyFinset [Finite G] {M K N : Subgroup G} :
    N ∈ ZFamilyFinset M K ↔ IsZFamilyMember M K N :=
  Set.Finite.mem_toFinset _

theorem ZFamilyFinset_nonempty [Finite G] {M K : Subgroup G} : (ZFamilyFinset M K).Nonempty :=
  ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl)⟩

/-- **BG 14.7, the `|T|` count for the family** (mmd L4031): with `T = Z − ⋃_{N} (Z ⊓ M_σ(N))`
over the family `ZFamilyFinset`, `|T| + ∑ |Kᵢ*| + 1 = |Z| + |family|` — i.e. `|T| = z + n − ∑ kᵢ*`
(`|family| = n + 1`).  Direct instance of inclusion–exclusion
(`ncard_sdiff_biUnion_subgroup`) with the pairwise disjointness `typeP_family_Kstar_disjoint`. -/
theorem typeP_family_T_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)).ncard
      + (∑ N ∈ ZFamilyFinset M K, Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)) + 1
      = Nat.card ↥(K ⊔ Kstar) + (ZFamilyFinset M K).card := by
  refine ncard_sdiff_biUnion_subgroup (s := ZFamilyFinset M K) (Z := K ⊔ Kstar)
    (S := fun N => (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)
    ZFamilyFinset_nonempty (fun _ _ => inf_le_left) ?_
  intro N₁ hN₁ N₂ hN₂ hne
  exact typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU
    (mem_ZFamilyFinset.mp hN₁) (mem_ZFamilyFinset.mp hN₂) hne

/-- **BG 14.7, each family factor `Kᵢ* ◁ Z`** (mmd L3995 "`N_{M_i}(X*) = K_i × K_i*`"): every member
`N` of the type-`P` family has its canonical factor `Z ⊓ M_σ(N)` normalised by all of `Z = K ⊔ K*`.
For `N = M` this is `typeP_self_member`; for a neighbour it is the normality clause of
`exists_neighbor_full`.  Feeds the `Z`-stability of `T` (`hstab` for the TI count). -/
theorem typeP_family_member_normal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    K ⊔ Kstar ≤ Subgroup.normalizer
      (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  rcases hN with hNM | ⟨p, X, hp, hX, hXK, hN⟩
  · rw [hNM]; exact (typeP_self_member hG hM hP hKM hK hKstar hU).2.2.1
  · haveI : Fact p.Prime := ⟨hp⟩
    have hCX : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      refine (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (le_bot_iff.mp ?_)
      rw [hKstar]
      calc OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
          ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXK))
        _ = ⊥ := hbot
    obtain ⟨_, _, _, _, hnorm, _, _⟩ :=
      exists_neighbor_full hG hM hP hKM hK hKstar hU hX hXK hCX hN
    exact hnorm

/-- **BG 14.7, the family `Kᵢ*` pairwise commute** (mmd L4009): for distinct members `N₁ ≠ N₂`, the
canonical factors `Z ⊓ M_σ(Nᵢ)` centralise each other — both are normalised by `Z`
(`typeP_family_member_normal`) and meet trivially (`typeP_family_Kstar_disjoint`), so their
commutator lies in their (trivial) intersection.  The commute input to
`card_iSup_of_pairwise_commute_coprime` for `z = ∏ kᵢ*`. -/
theorem typeP_family_Kstar_commute [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N₁ N₂ : Subgroup G} (hN₁ : IsZFamilyMember M K N₁) (hN₂ : IsZFamilyMember M K N₂)
    (hne : N₁ ≠ N₂) :
    ∀ x ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₁,
      ∀ y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N₂, Commute x y :=
  commute_of_le_normalizer_of_disjoint inf_le_left inf_le_left
    (typeP_family_member_normal hG hM hP hKM hK hKstar hU hN₁)
    (typeP_family_member_normal hG hM hP hKM hK hKstar hU hN₂)
    (typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU hN₁ hN₂ hne)

/-- **BG 14.7, `Z` normalises `T`** (mmd L4029, "`N_G(T) = Z`" half — the easy `Z ≤ N_G(T)` part):
conjugation by any `l ∈ Z = K ⊔ K*` fixes the set `T = Z − ⋃_{N} (Z ⊓ M_σ(N))`, because `l`
normalises `Z` (self-normalisation) and each canonical factor `Z ⊓ M_σ(N)`
(`typeP_family_member_normal`).  This is the `hstab` hypothesis of
`ncard_conjClassSet_of_isTISubset` once `T` is shown to be a TI-subset. -/
theorem typeP_family_Z_normalizes_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ l ∈ K ⊔ Kstar, MulAut.conj l •
        (((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      = ((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
  intro l hl
  rw [Set.smul_set_sdiff, Set.smul_set_iUnion₂]
  congr 1
  · rw [← Subgroup.coe_pointwise_smul,
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hl)]
  · refine Set.iUnion₂_congr (fun N hN => ?_)
    rw [← Subgroup.coe_pointwise_smul,
      conj_smul_eq_self_of_mem_normalizer
        (typeP_family_member_normal hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN) hl)]

/-- **BG Proposition 14.2(d), second assertion** (mmd L3827): for a type-`P` maximal `M` with Hall
`κ(M)`-subgroup `K` and `K* = C_{M_σ}(K)`, every `g ∈ M − (K ⊔ K*)` satisfies `K ∩ K^g = 1`.

BG: "the second assertion follows easily from (b1) since `K` is a Z-group."  Lean proof: a
nontrivial element of `K ∩ K^g` gives a rank-one `X = ⟨x⟩ ≤ K` of prime order `p` and its conjugate
`Y = ⟨g⁻¹ x g⟩ ≤ K`.  By Proposition 14.2(b1) (`typeP_structure`), `N_G(X) ⊓ M = N_G(Y) ⊓ M = Z`, so
`K` normalises both.  Since `g ∈ M` but `g ∉ Z`, `g ∉ N_G(X)`, hence `MulAut.conj g⁻¹ • X ≠ X`,
i.e. `X ≠ Y`.  Two distinct normal rank-one subgroups of `K` generate an elementary abelian `p²`
inside `M`, forcing `pRank_M(p) ≥ 2` — contradicting `pRank_M(p) = 1` (`p ∈ π(K) ⊆ κ(M) ⊆ τ₁ ∪ τ₃`).
This is the `(d)`-clause the TI-argument of Theorem 14.7 invokes (`g ∈ K_i × K_i*`). -/
theorem typeP_kappaHall_inf_conj_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {g : G} (hgM : g ∈ M) (hgZ : g ∉ K ⊔ Kstar) :
    K ⊓ (MulAut.conj g • K) = ⊥ := by
  classical
  by_contra hne
  -- A prime `p ∣ |K ∩ K^g|` and an order-`p` element `x ∈ K ∩ K^g`.
  have hcard_ne : Nat.card ↥(K ⊓ (MulAut.conj g • K)) ≠ 1 :=
    fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  haveI : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hxmem : (x : G) ∈ K ⊓ (MulAut.conj g • K) := x.2
  have hxK : (x : G) ∈ K := (Subgroup.mem_inf.mp hxmem).1
  have hxKg : (x : G) ∈ MulAut.conj g • K := (Subgroup.mem_inf.mp hxmem).2
  have hxord' : orderOf (x : G) = p :=
    (orderOf_injective (K ⊓ (MulAut.conj g • K)).subtype
      (K ⊓ (MulAut.conj g • K)).subtype_injective x).trans hxord
  have hxne1 : (x : G) ≠ 1 := fun h => hp_prime.ne_one (by rw [← hxord', h, orderOf_one])
  -- `X = ⟨x⟩ ≤ K`, rank-one.
  set X := Subgroup.zpowers (x : G) with hXdef
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers, hxord']
  have hXea : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXleK : X ≤ K := Subgroup.zpowers_le.mpr hxK
  -- `Y = ⟨g⁻¹ x g⟩ ≤ K`, rank-one (`g⁻¹ x g ∈ K` since `x ∈ K^g`).
  have hgxgK : g⁻¹ * (x : G) * g ∈ K := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxKg
    simpa [MulAut.smul_def] using hxKg
  set y₀ := g⁻¹ * (x : G) * g with hy₀def
  have hy₀conj : y₀ = (MulAut.conj g⁻¹).toMonoidHom (x : G) := by
    rw [hy₀def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hy₀ord : orderOf y₀ = p := by
    rw [hy₀conj, orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    exact hxord'
  set Y := Subgroup.zpowers y₀ with hYdef
  have hYcard : Nat.card ↥Y = p := by rw [hYdef, Nat.card_zpowers, hy₀ord]
  have hYea : Y ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYleK : Y ≤ K := Subgroup.zpowers_le.mpr hgxgK
  -- (b1): `N_G(X) ⊓ M = N_G(Y) ⊓ M = Z`, so `K` normalises both.
  have hb1 := (typeP_structure hG hM hP hKM hK hKstar hU).2.2.1
  have hNX : Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp_prime X hXea hXleK
  have hNY : Subgroup.normalizer (Y : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp_prime Y hYea hYleK
  have hKNX : K ≤ Subgroup.normalizer (X : Set G) :=
    le_trans (le_trans le_sup_left hNX.ge) inf_le_left
  have hKNY : K ≤ Subgroup.normalizer (Y : Set G) :=
    le_trans (le_trans le_sup_left hNY.ge) inf_le_left
  -- `X ≠ Y`: else `MulAut.conj g⁻¹ • X = Y = X`, so `g ∈ N_G(X) ⊓ M = Z`, against `g ∉ Z`.
  have hXneY : X ≠ Y := by
    intro hXeqY
    have hsmulXY : MulAut.conj g⁻¹ • X = Y := by
      rw [hXdef, hYdef, hy₀conj,
        show MulAut.conj g⁻¹ • Subgroup.zpowers (x : G)
          = (Subgroup.zpowers (x : G)).map (MulAut.conj g⁻¹).toMonoidHom from rfl,
        MonoidHom.map_zpowers]
    have hginvNX : g⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      mem_normalizer_of_conj_smul_eq_self (hsmulXY.trans hXeqY.symm)
    have hgNX : g ∈ Subgroup.normalizer (X : Set G) := by
      simpa using (Subgroup.normalizer (X : Set G)).inv_mem hginvNX
    exact hgZ (hNX ▸ Subgroup.mem_inf.mpr ⟨hgNX, hgM⟩)
  -- `X ⊓ Y = ⊥` (distinct rank-one subgroups of prime order `p`).
  have hXYbot : X ⊓ Y = ⊥ := by
    by_contra hb
    have hdvd : Nat.card ↥(X ⊓ Y) ∣ p := hXcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hne1 : Nat.card ↥(X ⊓ Y) ≠ 1 := fun h => hb (Subgroup.eq_bot_of_card_eq _ h)
    have hpeq : Nat.card ↥(X ⊓ Y) = p := ((Nat.dvd_prime hp_prime).mp hdvd).resolve_left hne1
    have hXY_eq_X : X ⊓ Y = X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (hXcard.le.trans hpeq.ge)
    exact hXneY (Subgroup.eq_of_le_of_card_ge (hXY_eq_X ▸ inf_le_right)
      (hYcard.le.trans hXcard.ge))
  -- `X`, `Y` commute (both normal in `K`, trivial meet), so `X ⊔ Y` is elementary abelian `p²`.
  have hcomm : ∀ a ∈ X, ∀ b ∈ Y, Commute a b :=
    commute_of_le_normalizer_of_disjoint hXleK hYleK hKNX hKNY hXYbot
  have hXcentY : X ≤ Subgroup.centralizer (Y : Set G) := fun a ha =>
    (Subgroup.mem_centralizer_iff).mpr fun b hb => (hcomm a ha b hb).symm
  have hsupea : (X ⊔ Y).IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hXea.1 hYea.1 hXcentY
  have hsupcard : Nat.card ↥(X ⊔ Y) = p ^ 2 := by
    rw [card_sup_of_commute_of_disjoint hcomm hXYbot, hXcard, hYcard]; ring
  -- `X ⊔ Y ≤ M`, witnessing `pRank_M(p) ≥ 2`.
  have hsupM : X ⊔ Y ≤ M := sup_le (hXleK.trans hKM) (hYleK.trans hKM)
  have hsubea : ((X ⊔ Y).subgroupOf M).IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsupM).symm hsupea
  have hsubcard : Nat.card ↥((X ⊔ Y).subgroupOf M) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsupM).toEquiv, hsupcard]
  have hle := le_pRank ((X ⊔ Y).subgroupOf M) hsubea
  rw [hsubcard, Nat.log_pow hp_prime.one_lt] at hle
  -- but `pRank_M(p) = 1` since `p ∈ π(K) ⊆ κ(M) ⊆ τ₁ ∪ τ₃`.
  have hp_kappa : p ∈ kappa M := by
    apply hK.1 p
    rw [Nat.mem_primeFactors]
    refine ⟨hp_prime, ?_, Nat.card_pos.ne'⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact hp_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hpRank1 : pRank ↥M p = 1 := by
    rcases kappa_subset_tau1_union_tau3 hp_kappa with h | h
    · exact tau1_pRank_eq_one h
    · exact tau3_pRank_eq_one h
  omega

/-- **BG 14.7, the family `σ(Nᵢ)` cover `π(z)`** (mmd L4007 "each `X ∈ ℰ¹(Z)` lies in some `Kᵢ*`"):
every prime `p ∣ |Z|` lies in `σ(N)` for some family member `N`.  For `p ∣ |K*|` it is the base
member `M` (`K* ≤ M_σ`, `Kstar_isPiSubgroup_sigma`); for `p ∣ |K|` (`p ∈ κ(M)`) a line
`X ∈ ℰ_p¹(K)` has a type-`P` partner `N ∈ 𝓜(N_G(X))` — a family member — with `X ⊆ M_σ(N)`, so
`p ∈ σ(N)`.  This coverage forces `⋂ᵢ Kᵢ = 1`, i.e. the `t = yy'` characterisation of `T`. -/
theorem typeP_family_sigma_covers [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {p : ℕ} (hp : p.Prime) (hpZ : p ∣ Nat.card ↥(K ⊔ Kstar)) :
    ∃ N : Subgroup G, IsZFamilyMember M K N ∧ p ∈ OddOrder.BG.Ch3.S10.sigma N := by
  classical
  rw [card_kappaHall_sup_Kstar hKM hK hKstar] at hpZ
  rcases hp.dvd_mul.mp hpZ with hpK | hpKstar
  · -- `p ∣ k`: a line `X ∈ ℰ_p¹(K)` and its type-`P` partner is a family member.
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
    have hxord : orderOf (x : G) = p :=
      (orderOf_injective K.subtype K.subtype_injective x).trans hx
    have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
    have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
    have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
    obtain ⟨N, hNmem, _, _, hXNσ, _, _⟩ :=
      exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
    refine ⟨N, Or.inr ⟨p, Subgroup.zpowers (x : G), hp, hXelem, hXK, hNmem⟩, ?_⟩
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hp, (by rw [hXcard] : p ∣ Nat.card ↥(Subgroup.zpowers (x : G))).trans
        (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)
  · -- `p ∣ k*`: the base member `M` itself, since `K* ≤ M_σ`.
    exact ⟨M, Or.inl rfl, Kstar_isPiSubgroup_sigma hKstar p
      (Nat.mem_primeFactors.mpr ⟨hp, hpKstar, Nat.card_pos.ne'⟩)⟩

/-- **BG 14.7, `Kᵢ*` is the `σ(Nᵢ)`-Hall of `Z`** (mmd L4007): for a family member `N` and a prime
`p ∈ σ(N)`, the full `p`-part of `|Z|` divides `|Kᵢ*| = |Z ⊓ M_σ(N)|`.  From the swap
`|Z| = |K_N|·|Kᵢ*|` (`card_kappaHall_sup_Kstar` on `N`'s data), `K_N` a `σ(N)'`-group
(`kappaHall_isPiSubgroup_sigmaCompl`), so `p ∤ |K_N|` and `pᵏ ∣ |Z|` forces `pᵏ ∣ |Kᵢ*|`.  Feeds
the σ-decomposition `⊔ Kᵢ* = Z`. -/
theorem typeP_family_prime_pow_dvd_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) {p k : ℕ} (hp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma N) (hpk : p ^ k ∣ Nat.card ↥(K ⊔ Kstar)) :
    p ^ k ∣ Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
  obtain ⟨_, _, _, KN, hKNN, hKN, hswap, hcanon, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  -- `|Z| = |K_N| · |Kᵢ*|`.
  have hZcard : Nat.card ↥(K ⊔ Kstar)
      = Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    have h := card_kappaHall_sup_Kstar hKNN hKN
      (rfl : OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)
        = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
    rw [← hswap, hcanon] at h
    exact h
  -- `p ∤ |K_N|` (a `σ(N)'`-group), so `pᵏ` is coprime to `|K_N|`.
  have hpKN : ¬ p ∣ Nat.card ↥KN := fun hd =>
    kappaHall_isPiSubgroup_sigmaCompl hKNN hKN p
      (Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.card_pos.ne'⟩) hpσ
  have hcop : Nat.Coprime (p ^ k) (Nat.card ↥KN) :=
    (hp.coprime_iff_not_dvd.mpr hpKN).pow_left k
  exact hcop.dvd_of_dvd_mul_left (hZcard ▸ hpk)

/-- **BG 14.7, the σ-decomposition `⊔ Kᵢ* = Z`** (mmd L4009): the canonical factors of the family
join to all of `Z`.  `⊔ Kᵢ* ≤ Z` is clear; for `Z ≤ ⊔ Kᵢ*` it suffices that `|Z| ∣ |⊔ Kᵢ*|`, which
holds prime-power-wise: for `pᵏ ∣ |Z|` the prime `p` lies in some `σ(N)`
(`typeP_family_sigma_covers`), and then `pᵏ ∣ |Kᵢ*|` (`typeP_family_prime_pow_dvd_Kstar`) `∣ |⊔ Kᵢ*|`.
With `⊔ Kᵢ* ≤ Z` this gives equality.  The structural heart of the TI-of-`T` step. -/
theorem typeP_family_iSup_Kstar_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ⨆ N ∈ ZFamilyFinset M K, ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) = K ⊔ Kstar := by
  have hsuple : (⨆ N ∈ ZFamilyFinset M K, ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
      ≤ K ⊔ Kstar := iSup₂_le fun _ _ => inf_le_left
  have hdvd : Nat.card ↥(K ⊔ Kstar)
      ∣ Nat.card ↥(⨆ N ∈ ZFamilyFinset M K, ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have hpZ : p ∣ Nat.card ↥(K ⊔ Kstar) := (dvd_pow_self p hkpos.ne').trans hpk
      obtain ⟨N, hN, hpσ⟩ := typeP_family_sigma_covers hG hM hP hKM hK hKstar hU hp hpZ
      exact (typeP_family_prime_pow_dvd_Kstar hG hM hP hKM hK hKstar hU hN hp hpσ hpk).trans
        (Subgroup.card_dvd_of_le
          (le_iSup₂ (f := fun N _ => (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) N
            (mem_ZFamilyFinset.mpr hN)))
  exact Subgroup.eq_of_le_of_card_ge hsuple (Nat.le_of_dvd Nat.card_pos hdvd)

/-- **BG 14.7, `σ(N)`-elements of `Z` lie in `Kᵢ*`** (mmd L4019, the `σ`-part lands in `Kᵢ*`): for a
family member `N`, every `σ(N)`-element `a ∈ Z` lies in `Kᵢ* = Z ⊓ M_σ(N)`.  Since `a ∈ Z ≤ N`, the
cyclic `⟨a⟩` is a `σ(N)`-subgroup of `N`, hence `⟨a⟩ ≤ M_σ(N)`
(`sigma_subgroup_le_Msigma_of_isHall`); combined with `a ∈ Z` this gives `a ∈ Z ⊓ M_σ(N)`.  This
places the `σ(N)`-part of any `t ∈ Z` into `Kᵢ*` — half of the `t = yy'` characterisation of `T`. -/
theorem typeP_family_isPiElement_mem_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) {a : G} (haZ : a ∈ K ⊔ Kstar)
    (hapi : IsPiElement (OddOrder.BG.Ch3.S10.sigma N) a) :
    a ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N := by
  obtain ⟨hNmax, _, hZN, _⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  refine Subgroup.mem_inf.mpr ⟨haZ, ?_⟩
  have hpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N) (Subgroup.zpowers a) := by
    intro p hp
    rw [Nat.card_zpowers] at hp
    exact hapi p hp
  exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax)
    (Subgroup.zpowers_le.mpr (hZN haZ)) hpi (Subgroup.mem_zpowers a)

/-- **An internal direct factor absorbs coprime elements** (BG 14.7, the `σ(N)′`-part lands in
`K_N`): if `Z = A ⊔ B` with `B ≤ C_G(A)` (so `A`, `B` commute), `A` a `πᶜ`-group and `B` a
`π`-group, then every `πᶜ`-element of `Z` lies in `A`.  Proof: `A ◁ Z` (commuting factor) is a Hall
`πᶜ`-subgroup of `Z` (`|Z| = |A|·|B|`, index `= |B|` a `π`-number), so the `πᶜ`-group `⟨b⟩ ≤ Z` lies
in `A` (`isPiGroup_le_of_normal_isHallSubgroup` in `↥Z`).  Applied with `A = K_N` (the `σ(N)′`-Hall
of `Z`), `B = Kᵢ*`, `π = σ(N)`: the `σ(N)′`-part of any `t ∈ Z` lands in `K_N`. -/
theorem isPiElementCompl_mem_left_of_commute [Finite G] {A B Z : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    {b : G} (hbZ : b ∈ Z) (hbπc : IsPiElement πᶜ b) : b ∈ A := by
  classical
  have hAZ : A ≤ Z := by rw [hswap]; exact le_sup_left
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, Commute a c := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hcent hc) a ha
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact (hAπc p (Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩))
      (hBπ p (Nat.mem_primeFactors.mpr ⟨hp, hpB, Nat.card_pos.ne'⟩))
  have hdisj : A ⊓ B = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hnorm : Z ≤ Subgroup.normalizer (A : Set G) := by
    rw [hswap]; exact (sup_le_normalizer_inf_of_commute hcent).trans inf_le_left
  haveI hAnZ : (A.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAZ).mpr hnorm
  have hZcard : Nat.card ↥Z = Nat.card ↥A * Nat.card ↥B := by
    rw [hswap]; exact card_sup_of_commute_of_disjoint hcomm hdisj
  have hcardSub : Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hidx : (A.subgroupOf Z).index = Nat.card ↥B := by
    have hl := Subgroup.card_mul_index (A.subgroupOf Z)
    rw [hcardSub, hZcard] at hl
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hl
  have hHall : Ch03.IsHallSubgroup πᶜ (A.subgroupOf Z) := by
    refine ⟨fun p hp => ?_, fun p hp hpc => ?_⟩
    · rw [hcardSub] at hp; exact hAπc p hp
    · exact hpc (hBπ p (by rwa [hidx] at hp))
  have hbZsub : (Subgroup.zpowers b).subgroupOf Z ≤ A.subgroupOf Z := by
    refine OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall (fun p hp => ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hbZ)).toEquiv, Nat.card_zpowers] at hp
    exact hbπc p hp
  have hbmem : (⟨b, hbZ⟩ : ↥Z) ∈ (Subgroup.zpowers b).subgroupOf Z :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b)
  exact Subgroup.mem_subgroupOf.mp (hbZsub hbmem)

/-- **BG 14.7, the family member's `(d)`-data bundle** (mmd L3827, both clauses of Prop 14.2(d)):
for a family member `N`, the chosen Hall `κ(N)`-subgroup `K_N` together with the swap
`Z = K_N ⊔ Kᵢ*` and both conjugacy clauses — (d)-first `Kᵢ* ⊓ Nᵍ = 1` (`g ∉ N`) and (d)-second
`K_N ⊓ K_Nᵍ = 1` (`g ∈ N`, `g ∉ Z`).  Builds `N`'s Hall `(κ∪σ)′`-subgroup once
(`hall_E_exists`, `N` solvable) and feeds it to `typeP_structure` (d-first) and
`typeP_kappaHall_inf_conj_eq_bot` (d-second).  The TI-of-`T` proof obtains this once per chosen
member and conjugates the `σ`/`σ′`-parts of `t` through the two clauses to force `g ∈ Z`. -/
theorem typeP_family_member_dData [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    ∃ KN : Subgroup G, KN ≤ N ∧ Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N) ∧
      K ⊔ Kstar = KN ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∧
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ≤ Subgroup.centralizer (KN : Set G) ∧
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)ᶜ KN ∧
      (∀ g : G, g ∉ N →
        ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ⊓ (MulAut.conj g • N) = ⊥) ∧
      (∀ g : G, g ∈ N → g ∉ K ⊔ Kstar → KN ⊓ (MulAut.conj g • KN) = ⊥) := by
  classical
  obtain ⟨hNmax, hPN, _, KN, hKNN, hKN, hswap, hcanon, _⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  haveI : IsSolvable ↥N := hG.solvable_of_mem_maximalSubgroups hNmax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥N)
    ((kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
  have hUeq : (U'.map N.subtype).subgroupOf N = U' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective U'
  have hUN : Ch03.IsHallSubgroup ((kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ)
      ((U'.map N.subtype).subgroupOf N) := by rw [hUeq]; exact hU'
  refine ⟨KN, hKNN, hKN, hswap.trans (by rw [hcanon]), hcanon ▸ inf_le_right,
    kappaHall_isPiSubgroup_sigmaCompl hKNN hKN, ?_, ?_⟩
  · intro g hgN
    have hd := (typeP_structure hG hNmax hPN hKNN hKN rfl hUN).2.2.2.1
    rw [hcanon] at hd
    exact hd g hgN
  · intro g hgN hgZ
    exact typeP_kappaHall_inf_conj_eq_bot hG hNmax hPN hKNN hKN rfl hUN hgN (hswap ▸ hgZ)

/-- **BG 14.7, every nontrivial `t ∈ Z` has a nontrivial `σ`-part** (mmd L4015, `z = ∏ xᵢ` is the
`σ`-decomposition): for `t ∈ Z`, `t ≠ 1`, some family member `N` has `t` *not* a `σ(N)′`-element
(equivalently its `σ(N)`-part is nontrivial).  Else every prime of `ord(t)` avoids every `σ(N)`,
contradicting the coverage `⋃ σ(Nᵢ) ⊇ π(z)` (`typeP_family_sigma_covers`) since `ord(t) ∣ |Z|`.
This is the half of the `t = yy'` characterisation that finds the splitting member. -/
theorem typeP_family_exists_sigmaPart [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {t : G} (htZ : t ∈ K ⊔ Kstar) (ht1 : t ≠ 1) :
    ∃ N : Subgroup G, IsZFamilyMember M K N ∧
      ¬ IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ t := by
  by_contra hcon
  push Not at hcon
  -- `ord(t) ≠ 1` has a prime factor `p`, and `p ∣ |Z|`.
  have hordne : orderOf t ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact ht1
  obtain ⟨p, hp, hpord⟩ := Nat.exists_prime_and_dvd hordne
  have hpz : p ∣ Nat.card ↥(K ⊔ Kstar) := by
    refine hpord.trans ?_
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr htZ)
    rwa [Nat.card_zpowers] at this
  obtain ⟨N, hN, hpσN⟩ := typeP_family_sigma_covers hG hM hP hKM hK hKstar hU hp hpz
  exact hcon N hN p (Nat.mem_primeFactors.mpr ⟨hp, hpord, (orderOf_pos t).ne'⟩) hpσN

/-- **BG 14.7, `T` is a TI-subset of `G` with normalizer `Z`** (mmd L4027-4029): `T = Z − ⋃ Kᵢ*`
satisfies `IsTISubset T Z`.  Given `t ∈ T` and `g` with `tᵍ ∈ T ⊆ Z`: pick a member `N` whose
`σ(N)`-part of `t` is nontrivial (`typeP_family_exists_sigmaPart`), `π`-decompose `t = y·y'`
(`exists_isPiElement_mul`, `π = σ(N)`) with `y ∈ Kᵢ*` (`…isPiElement_mem_Kstar`) and `y' ∈ K_N`
(`isPiElementCompl_mem_left_of_commute`), both nontrivial (`y` by choice of `N`, `y'` since
`t ∉ Kᵢ*`).  Conjugates `yᵍ, y'ᵍ` are powers of `tᵍ ∈ Z`, so `yᵍ ∈ Kᵢ*`, `y'ᵍ ∈ K_N`; then
`yᵍ ∈ Kᵢ* ∩ Nᵍ` forces `g ∈ N` (Prop 14.2(d)-first) and `y'ᵍ ∈ K_N ∩ K_Nᵍ` forces `g ∈ Z`
(d-second).  The structural core converting `|T|` to `|𝒞_G(T)| = |T|·[G:Z]`. -/
theorem typeP_family_T_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    OddOrder.GroupTheory.IsTISubset
      (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      (K ⊔ Kstar) := by
  classical
  rintro g ⟨t, ⟨htZ, htnot⟩, ⟨htgZ, -⟩⟩
  -- `t ∈ Z`, `t ∉ ⋃ Kⱼ*`, `g t g⁻¹ ∈ Z`.
  have htZ' : t ∈ K ⊔ Kstar := htZ
  have htgZ' : g * t * g⁻¹ ∈ K ⊔ Kstar := htgZ
  have ht1 : t ≠ 1 := fun h => htnot
    (Set.mem_biUnion (mem_ZFamilyFinset.mpr (Or.inl rfl)) (h ▸ one_mem _))
  -- Conjugation by `g` keeps powers of `t` inside `Z` and preserves `π`-element-ness.
  have hconjZ : ∀ a : G, a ∈ Subgroup.zpowers t → g * a * g⁻¹ ∈ K ⊔ Kstar := by
    intro a ha
    refine (Subgroup.zpowers_le.mpr htgZ') ?_
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
    rw [MonoidHom.map_zpowers] at h1
    simpa [MulAut.conj_apply] using h1
  have hordeq : ∀ a : G, orderOf (g * a * g⁻¹) = orderOf a := fun a => by
    rw [show g * a * g⁻¹ = (MulAut.conj g).toMonoidHom a by simp [MulAut.conj_apply]]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  have hpiconj : ∀ {π : Set ℕ} {a : G}, IsPiElement π a → IsPiElement π (g * a * g⁻¹) :=
    fun {π a} ha p hp => ha p (by rwa [hordeq a] at hp)
  -- Pick a member `N` with nontrivial `σ(N)`-part, and `π`-decompose `t`.
  obtain ⟨N, hN, hσpart⟩ := typeP_family_exists_sigmaPart hG hM hP hKM hK hKstar hU htZ' ht1
  obtain ⟨y, y', hyy', hcomm, hyπ, hy'π, hyz, hy'z⟩ :=
    exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma N) t
  have hyZ : y ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ') hyz
  have hy'Z : y' ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ') hy'z
  obtain ⟨KN, hKNN, _, hswap, hcent, hAπc, hdfirst, hdsecond⟩ :=
    typeP_family_member_dData hG hM hP hKM hK hKstar hU hN
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  -- `y ∈ Kᵢ*`, `y' ∈ K_N`; both nontrivial.
  have hyKstar : y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hyZ hyπ
  have hy'KN : y' ∈ KN := isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'Z hy'π
  have hy1 : y ≠ 1 := by
    rintro rfl; exact hσpart (by rw [show t = y' from by rw [← hyy', one_mul]]; exact hy'π)
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    exact htnot (Set.mem_biUnion (mem_ZFamilyFinset.mpr hN)
      (show t ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) from
        by rw [show t = y from by rw [← hyy', mul_one]]; exact hyKstar))
  -- `yᵍ ∈ Kᵢ*` (a `σ(N)`-element of `Z`), `yᵍ ≠ 1`; force `g ∈ N` via (d)-first.
  have hygZ : g * y * g⁻¹ ∈ K ⊔ Kstar := hconjZ y hyz
  have hygKstar : g * y * g⁻¹ ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hygZ (hpiconj hyπ)
  have hyg1 : g * y * g⁻¹ ≠ 1 := fun h =>
    hy1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp (by rw [MulAut.conj_apply]; exact h))
  have hgN : g ∈ N := by
    by_contra hgnot
    have hbot := hdfirst g hgnot
    have hmem : g * y * g⁻¹ ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ⊓ (MulAut.conj g • N) := by
      refine Subgroup.mem_inf.mpr ⟨hygKstar, ?_⟩
      have hyN : y ∈ N := (inf_le_right.trans (OddOrder.BG.Ch3.S10.Msigma_le N)) hyKstar
      rw [show (MulAut.conj g • N : Subgroup G) = N.map (MulAut.conj g).toMonoidHom from rfl,
        show g * y * g⁻¹ = (MulAut.conj g).toMonoidHom y from by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
      exact Subgroup.mem_map_of_mem _ hyN
    rw [hbot] at hmem
    exact hyg1 (Subgroup.mem_bot.mp hmem)
  -- `y'ᵍ ∈ K_N ∩ K_Nᵍ`, `y'ᵍ ≠ 1`; force `g ∈ Z` via (d)-second.
  have hy'gZ : g * y' * g⁻¹ ∈ K ⊔ Kstar := hconjZ y' hy'z
  have hy'gKN : g * y' * g⁻¹ ∈ KN :=
    isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'gZ (hpiconj hy'π)
  have hy'g1 : g * y' * g⁻¹ ≠ 1 := fun h =>
    hy'1 ((map_eq_one_iff _ (MulAut.conj g).injective).mp (by rw [MulAut.conj_apply]; exact h))
  by_contra hgZ
  have hbot := hdsecond g hgN hgZ
  have hmem : g * y' * g⁻¹ ∈ KN ⊓ (MulAut.conj g • KN) := by
    refine Subgroup.mem_inf.mpr ⟨hy'gKN, ?_⟩
    rw [show (MulAut.conj g • KN : Subgroup G) = KN.map (MulAut.conj g).toMonoidHom from rfl,
      show g * y' * g⁻¹ = (MulAut.conj g).toMonoidHom y' from by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
    exact Subgroup.mem_map_of_mem _ hy'KN
  rw [hbot] at hmem
  exact hy'g1 (Subgroup.mem_bot.mp hmem)

/-- **BG 14.7, `|𝒞_G(T)| = |T|·[G:Z]`** (mmd L4031): the conjugacy-saturation count of the TI-set
`T = Z − ⋃ Kᵢ*`.  Direct composition of `ncard_conjClassSet_of_isTISubset` with the TI property
(`typeP_family_T_isTI`) and the `Z`-stability `hstab` (`typeP_family_Z_normalizes_T`).  With
`|T| = z + n − ∑ kᵢ*` (`typeP_family_T_count`) this is BG's `(1 + n/z − ∑ 1/kᵢ)|G|`, the left
summand of the density inequality. -/
theorem typeP_family_conjClass_T_count [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))).ncard
      = (((K ⊔ Kstar : Subgroup G) : Set G) \
          ⋃ N ∈ ZFamilyFinset M K,
            (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)).ncard
        * (K ⊔ Kstar).index :=
  ncard_conjClassSet_of_isTISubset
    (typeP_family_T_isTI hG hM hP hKM hK hKstar hU)
    (typeP_family_Z_normalizes_T hG hM hP hKM hK hKstar hU)

/-- **BG 14.7, `Z ⊊ Mᵢ` (so `|Mᵢ| ≥ 2z`)** (mmd L4033, the `|M_i| ≥ 2z` step): every family member
`N` properly contains `Z = K ⊔ K*`.  The clean argument (NOT self-centralizing — BG's "prime
manner" allows trivial action): the family has `≥ 2` members (`M` plus a neighbour, which exists
since `N_G(X) ⊄ M` for `X ∈ ℰ¹(K)`), all containing `Z`; if `Z = N` then `N ⊆ M'` for some other
member `M' ≠ N`, impossible for distinct maximal subgroups.  Hence `Z ⊊ N`, giving `|N| ≥ 2z`. -/
theorem typeP_family_Z_lt_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    K ⊔ Kstar < N := by
  classical
  -- Distinct maximal subgroups form an antichain.
  have hanti : ∀ {A B : Subgroup G}, A ∈ maximalSubgroups G → B ∈ maximalSubgroups G →
      A ≤ B → A = B := fun {A B} hA hB hAB => hAB.lt_or_eq.elim
    (fun hlt => absurd ((mem_maximalSubgroups.mp hA).2 _ hlt) (mem_maximalSubgroups.mp hB).1) id
  -- A prime `p ∣ |K|` (κ(M) ≠ ∅, κ-primes divide |M|, Hall index avoids κ).
  have hP2 := hP
  obtain ⟨p, hpκ⟩ := hP2
  have hpprime : p.Prime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  -- A neighbour `N₁ ≠ M` containing `Z`.
  obtain ⟨N₁, hN₁max, -, hncM, -, hZN₁⟩ :=
    exists_typeP_neighbor_mem_sigma hG hM hP hKM hK hKstar hU hpprime hpK
  have hN₁neM : N₁ ≠ M := fun h =>
    hncM (h ▸ (⟨1, by rw [map_one, one_smul]⟩ : IsConjugateSubgroup M M))
  obtain ⟨hNmax, -, hZN, -⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have hZM : K ⊔ Kstar ≤ M :=
    sup_le hKM (hKstar ▸ inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  refine lt_of_le_of_ne hZN (fun heq => ?_)
  by_cases hNM : N = M
  · exact hN₁neM ((hanti hNmax hN₁max (heq ▸ hZN₁)).symm.trans hNM)
  · exact hNM (hanti hNmax hM (heq ▸ hZM))

/-- **BG 14.7, `|Mᵢ| ≥ 2z`** (mmd L4033): the cardinality form of `Z ⊊ Mᵢ`, the lower bound the
density inequality needs (`|𝒞_G(M̃ᵢ)| ≥ (1/kᵢ − 1/2z)|G|`).  From `Z < N` (proper), `[N : Z] ≥ 2`. -/
theorem typeP_family_two_mul_card_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    2 * Nat.card ↥(K ⊔ Kstar) ≤ Nat.card ↥N := by
  classical
  have hlt := typeP_family_Z_lt_member hG hM hP hKM hK hKstar hU hN
  have hle : K ⊔ Kstar ≤ N := hlt.le
  have hlag : Nat.card ↥(K ⊔ Kstar) * ((K ⊔ Kstar).subgroupOf N).index = Nat.card ↥N := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact Subgroup.card_mul_index ((K ⊔ Kstar).subgroupOf N)
  have hne1 : ((K ⊔ Kstar).subgroupOf N).index ≠ 1 := fun h =>
    hlt.ne (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h)))
  have hidx2 : 2 ≤ ((K ⊔ Kstar).subgroupOf N).index :=
    (Nat.two_le_iff _).mpr ⟨Subgroup.index_ne_zero_of_finite, hne1⟩
  calc 2 * Nat.card ↥(K ⊔ Kstar)
      ≤ ((K ⊔ Kstar).subgroupOf N).index * Nat.card ↥(K ⊔ Kstar) :=
        Nat.mul_le_mul_right _ hidx2
    _ = Nat.card ↥(K ⊔ Kstar) * ((K ⊔ Kstar).subgroupOf N).index := Nat.mul_comm _ _
    _ = Nat.card ↥N := hlag

/-- **`σ`-sharp set is conjugation-equivariant**: `conj g • (M_σ^#) = (M^g)_σ^#`.  From
`Msigma_conj_smul` (`M_σ` equivariant) and `conj g` fixing `1`. -/
theorem sigmaSharp_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    MulAut.conj g • sigmaSharp M = sigmaSharp (MulAut.conj g • M) := by
  rw [sigmaSharp, sigmaSharp, sharpSubgroup, sharpSubgroup, Set.smul_set_sdiff,
    ← Subgroup.coe_pointwise_smul, ← Msigma_conj_smul]
  congr 1
  simp [Set.smul_set_singleton, MulAut.smul_def]

/-- **`M̃` is conjugation-equivariant** (mmd L3908): `conj g • M̃(M) = M̃(Mᵍ)`.  Each product
`x·x'` (`x ∈ M_σ^#`, `x' ∈ R(x)`) conjugates to `(xᵍ)(x'ᵍ)` with `xᵍ ∈ (Mᵍ)_σ^#`
(`sigmaSharp_conj_smul`) and `x'ᵍ ∈ R(xᵍ)` (`Rsub_conj`).  This is what turns the set-level
disjointness 14.5(b) into disjointness of the conjugacy saturations `𝒞_G(M̃ᵢ)`. -/
theorem Mtilde_conj_smul [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (g : G) (M : Subgroup G) :
    MulAut.conj g • Mtilde hG D M = Mtilde hG D (MulAut.conj g • M) := by
  have hle : ∀ (h : G) (N : Subgroup G),
      MulAut.conj h • Mtilde hG D N ⊆ Mtilde hG D (MulAut.conj h • N) := by
    rintro h N y ⟨z, ⟨x, hx, x', hx', rfl⟩, rfl⟩
    refine ⟨MulAut.conj h • x, ?_, MulAut.conj h • x', ?_, ?_⟩
    · rw [← sigmaSharp_conj_smul]; exact Set.smul_mem_smul_set hx
    · rw [show MulAut.conj h • x = h * x * h⁻¹ from by rw [MulAut.smul_def, MulAut.conj_apply],
        Rsub_conj]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hx'
    · exact smul_mul' _ _ _
  refine Set.Subset.antisymm (hle g M) (fun y hy => ?_)
  have h2 := hle g⁻¹ (MulAut.conj g • M)
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h2
  have hmem : MulAut.conj g⁻¹ • y ∈ Mtilde hG D M := h2 (Set.smul_mem_smul_set hy)
  rw [show y = MulAut.conj g • (MulAut.conj g⁻¹ • y) by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]]
  exact Set.smul_mem_smul_set hmem

/-- **BG 14.7, the `𝒞_G(M̃ᵢ)` are pairwise disjoint** (mmd L4035): for nonconjugate maximal
`M₁`, `M₂`, the conjugacy saturations `𝒞_G(M̃₁)`, `𝒞_G(M̃₂)` are disjoint.  A common element `z`
is `g₁t₁g₁⁻¹ = g₂t₂g₂⁻¹` with `tᵢ ∈ M̃(Mᵢ)`, so `z ∈ M̃(M₁ᵍ¹) ∩ M̃(M₂ᵍ²)` (`Mtilde_conj_smul`);
`M₁ᵍ¹`, `M₂ᵍ²` are nonconjugate (else `M₁ ~ M₂`), so 14.5(b) (`Mtilde_disjoint`) gives a
contradiction.  Pairwise disjointness of the density-inequality summands. -/
theorem conjClassSet_Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ maximalSubgroups G)
    (hM₂ : M₂ ∈ maximalSubgroups G) (hnc : ¬ IsConjugateSubgroup M₁ M₂) :
    Disjoint (conjClassSet (Mtilde hG D M₁)) (conjClassSet (Mtilde hG D M₂)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t₁, ht₁, g₁, rfl⟩ ⟨t₂, ht₂, g₂, hz₂⟩
  have hz1 : g₁ * t₁ * g₁⁻¹ ∈ Mtilde hG D (MulAut.conj g₁ • M₁) := by
    rw [show g₁ * t₁ * g₁⁻¹ = MulAut.conj g₁ • t₁ from by rw [MulAut.smul_def, MulAut.conj_apply],
      ← Mtilde_conj_smul]
    exact Set.smul_mem_smul_set ht₁
  have hz2 : g₁ * t₁ * g₁⁻¹ ∈ Mtilde hG D (MulAut.conj g₂ • M₂) := by
    rw [← hz₂, show g₂ * t₂ * g₂⁻¹ = MulAut.conj g₂ • t₂ from by
      rw [MulAut.smul_def, MulAut.conj_apply], ← Mtilde_conj_smul]
    exact Set.smul_mem_smul_set ht₂
  have hc1 : IsConjugateSubgroup M₁ (MulAut.conj g₁ • M₁) := ⟨g₁, rfl⟩
  have hc2 : IsConjugateSubgroup M₂ (MulAut.conj g₂ • M₂) := ⟨g₂, rfl⟩
  have hncc : ¬ IsConjugateSubgroup (MulAut.conj g₁ • M₁) (MulAut.conj g₂ • M₂) := fun h =>
    hnc ((hc1.trans h).trans hc2.symm)
  exact Set.disjoint_left.mp (Mtilde_disjoint hG D
    (mem_maximalSubgroups_of_isConjugateSubgroup hM₁ ⟨g₁, rfl⟩)
    (mem_maximalSubgroups_of_isConjugateSubgroup hM₂ ⟨g₂, rfl⟩) hncc) hz1 hz2

/-- **`M̃`-membership is the `not_type1_of_type2` "type-2 form"**: `g ∈ M̃(M)` (for maximal `M`)
gives `g = x·x'` with `ℓ_σ(x) = 1` and `x' ∈ R(x)`.  The `ℓ_σ(x) = 1` is from `length_one_iff`
(`x ∈ M_σ^#`, so `M ∈ 𝓜_σ(x)`).  Feeds the `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)` disjointness via Lemma 14.6. -/
theorem mem_Mtilde_imp_form [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G}
    (hg : g ∈ Mtilde hG D M) :
    ∃ x x' : G, g = x * x' ∧ D.length x = 1 ∧ x' ∈ Rsub hG D x := by
  obtain ⟨x, hx, x', hx', rfl⟩ := hg
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hx
  exact ⟨x, x', rfl, (D.length_one_iff x).mpr ⟨hx.2, ⟨M, hM, hx.1⟩⟩, hx'⟩

/-- **Elements of `M̃` have `σ`-length at most two** (the per-element core of BG Cor 14.10): every
`g ∈ M̃(M) = ⋃_{x ∈ M_σ#} x·R(x)` is a `σ`-cover element `x·x'` (`mem_Mtilde_imp_form`) with
`x ∈ M_σ#` and `x' ∈ R(x)`, so `ℓ_σ(g) ≤ 2`.  In the multi-maximal case `R(x) = N_σ ∩ C_G(x)` for
the neighbour `N` (`exists_neighbor_eq_Rsub`), where `sigmaLength_cover_le_two_signalizer` applies;
in the trivial case `R(x) = 1`, so `g = x` with `ℓ_σ(x) = 1`. -/
theorem sigmaLength_le_two_of_mem_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G}
    (hg : g ∈ Mtilde hG (genuineSigmaDecomposition hG) M) :
    sigmaLength g ≤ 2 := by
  obtain ⟨x, x', rfl, hlen, hx'⟩ :=
    mem_Mtilde_imp_form hG (genuineSigmaDecomposition hG) hM hg
  have hx1 : x ≠ 1 := (((genuineSigmaDecomposition hG).length_one_iff x).mp hlen).1
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · obtain ⟨M0, hM0⟩ := (((genuineSigmaDecomposition hG).length_one_iff x).mp hlen).2
    obtain ⟨N, hNmax, _, hReq, hxτ2, _⟩ :=
      exists_neighbor_eq_Rsub hG (genuineSigmaDecomposition hG) hlen hgt
    rw [hReq] at hx'
    have hx'N : x' ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hx').1
    have hcomm : Commute x x' := by
      have h := (Subgroup.mem_inf.mp hx').2
      rw [Subgroup.mem_centralizer_iff] at h
      exact h x (Set.mem_singleton_iff.mpr rfl)
    exact sigmaLength_cover_le_two_signalizer hG hM0.1 hNmax hM0.2 hx1 hxτ2 hx'N hcomm
  · have hRbot : Rsub hG (genuineSigmaDecomposition hG) x = ⊥ := by
      unfold Rsub
      exact dif_neg (fun h => hgt h.2.2)
    rw [hRbot, Subgroup.mem_bot] at hx'
    rw [hx', mul_one]
    have hsl1 : sigmaLength x = 1 := hlen
    omega

/-- **BG 14.7, elements of `T` have the `not_type1_of_type2` "type-1 form"** (mmd L4021): for
`t ∈ T = Z − ⋃ Kᵢ*`, there is a family member `N` and `t = y·y'` with `y ∈ M_σ(N)^#`, `y'` a
nonidentity `κ(N)`-element of `N` centralising `y`.  Extracted exactly as in the TI-of-`T` proof:
the splitting member `N` (`typeP_family_exists_sigmaPart`), `π`-decompose `t = y·y'`
(`exists_isPiElement_mul`), `y ∈ Kᵢ* ≤ M_σ(N)` (`…isPiElement_mem_Kstar`) and `y' ∈ K_N` (a Hall
`κ(N)`-subgroup, `isPiElementCompl_mem_left_of_commute`), both nontrivial.  Feeds Lemma 14.6
(`not_type1_of_type2`) for the `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)` disjointness. -/
theorem typeP_family_T_form [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {t : G} (htT : t ∈ ((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧ ∃ y y' : G, t = y * y' ∧ Commute y y' ∧
      y ∈ sigmaSharp N ∧ y' ≠ 1 ∧ y' ∈ N ∧ y' ∈ Subgroup.centralizer ({y} : Set G) ∧
      ∀ p ∈ piSet (Subgroup.closure ({y'} : Set G)), p ∈ kappa N := by
  classical
  obtain ⟨htZ, htnot⟩ := htT
  have ht1 : t ≠ 1 := fun h => htnot
    (Set.mem_biUnion (mem_ZFamilyFinset.mpr (Or.inl rfl)) (h ▸ one_mem _))
  obtain ⟨N, hN, hσpart⟩ := typeP_family_exists_sigmaPart hG hM hP hKM hK hKstar hU htZ ht1
  obtain ⟨y, y', hyy', hcomm, hyπ, hy'π, hyz, hy'z⟩ :=
    exists_isPiElement_mul (OddOrder.BG.Ch3.S10.sigma N) t
  have hyZ : y ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hyz
  have hy'Z : y' ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hy'z
  obtain ⟨KN, hKNN, hKN, hswap, hcent, hAπc, -, -⟩ :=
    typeP_family_member_dData hG hM hP hKM hK hKstar hU hN
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
  have hyKstar : y ∈ (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N :=
    typeP_family_isPiElement_mem_Kstar hG hM hP hKM hK hKstar hU hN hyZ hyπ
  have hy'KN : y' ∈ KN := isPiElementCompl_mem_left_of_commute hswap hcent hAπc hBπ hy'Z hy'π
  have hy1 : y ≠ 1 := fun h =>
    hσpart (by rw [show t = y' from by rw [← hyy', h, one_mul]]; exact hy'π)
  have hy'1 : y' ≠ 1 := fun h => htnot (Set.mem_biUnion (mem_ZFamilyFinset.mpr hN)
    (show t ∈ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) from by
      rw [show t = y from by rw [← hyy', h, mul_one]]; exact hyKstar))
  obtain ⟨hNmax, -, -, -⟩ := typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  refine ⟨N, hNmax, y, y', hyy'.symm, hcomm, ?_, hy'1, hKNN hy'KN, ?_, ?_⟩
  · rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    exact ⟨(inf_le_right :
      (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≤ _) hyKstar, hy1⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw; rw [Set.mem_singleton_iff] at hw; subst hw; exact hcomm
  · intro p hp
    simp only [piSet, Set.mem_setOf_eq] at hp
    obtain ⟨hpp, hpdc, -⟩ := Nat.mem_primeFactors.mp hp
    have hpKN : p ∣ Nat.card ↥KN := hpdc.trans (Subgroup.card_dvd_of_le
      (by rw [← Subgroup.zpowers_eq_closure]; exact Subgroup.zpowers_le.mpr hy'KN))
    apply hKN.1 p
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNN).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpKN, Nat.card_pos.ne'⟩

/-- **BG 14.7, `𝒞_G(T)` is disjoint from each `𝒞_G(M̃ᵢ)`** (mmd L4025): the TI-set's conjugacy
saturation meets no `𝒞_G(M̃ᵢ)`.  A common `z = g₁tg₁⁻¹ = g₂sg₂⁻¹` (`t ∈ T`, `s ∈ M̃ᵢ`) makes
`t = (g₁⁻¹g₂)·s·(g₁⁻¹g₂)⁻¹` a conjugate of `s ∈ M̃ᵢ`, so `t ∈ M̃(Mᵢ^{g₁⁻¹g₂})` (`Mtilde_conj_smul`)
has the type-2 form (`mem_Mtilde_imp_form`); but `t ∈ T` has the type-1 form
(`typeP_family_T_form`), contradicting Lemma 14.6 (`not_type1_of_type2`).  The last disjointness
needed for the density inequality. -/
theorem conjClassSet_T_Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Mi : Subgroup G} (hMi : Mi ∈ maximalSubgroups G) :
    Disjoint (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G)))
      (conjClassSet (Mtilde hG D Mi)) := by
  rw [Set.disjoint_left]
  rintro z ⟨t, htT, g₁, rfl⟩ ⟨s, hsM, g₂, hz₂⟩
  obtain ⟨N, hNmax, y, y', hgyy', hcomm, hy, hy'1, hy'N, hy'C, hy'κ⟩ :=
    typeP_family_T_form hG hM hP hKM hK hKstar hU htT
  have heq : t = MulAut.conj (g₁⁻¹ * g₂) • s := by
    rw [MulAut.smul_def, MulAut.conj_apply,
      show (g₁⁻¹ * g₂) * s * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * s * g₂⁻¹) * g₁ from by group, hz₂]
    group
  have htM : t ∈ Mtilde hG D (MulAut.conj (g₁⁻¹ * g₂) • Mi) := by
    rw [← Mtilde_conj_smul, heq]; exact Set.smul_mem_smul_set hsM
  obtain ⟨x, x'', htxx, hlenx, hx''R⟩ := mem_Mtilde_imp_form hG D
    (mem_maximalSubgroups_of_isConjugateSubgroup hMi ⟨g₁⁻¹ * g₂, rfl⟩) htM
  exact not_type1_of_type2 hG D hNmax hy hgyy' hcomm hy'1 hy'N hy'C hy'κ ⟨x, x'', htxx, hlenx, hx''R⟩

/-- **BG 14.7, type-`P₁` Hall complement card** (mmd L4039, "`Kᵢ` complements `M_{iσ}` in `M_i`"):
for a type-`P₁` maximal subgroup `N` with a Hall `κ(N)`-subgroup `K_N ≤ N`, the order factors as
`|N| = |N_σ|·|K_N|`.  For type `P₁`, `κ(N) = π(N) − σ(N)`, so `K_N` is a Hall `σ(N)′`-subgroup
complementing the normal Hall `σ(N)`-subgroup `N_σ` (`Msigma_isHall`).  The proof is the σ-part
uniqueness: with `m = |N_σ|`, `j = [N : N_σ]`, `a = |K_N|`, `j' = [N : K_N]`, one has
`m·j = |N| = a·j'` with `m`, `j'` being `σ`-numbers and `a`, `j` being `σ′`-numbers, so `a = j`.
This is the `[N : N_σ] = kᵢ` identity the density inequality of Theorem 14.7(e) uses to rewrite
`(|N_σ| − 1)·[G : N]` as `(1/kᵢ − 1/|N|)·|G|`. -/
theorem typeP1_card_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N KN : Subgroup G} (hNmax : N ∈ maximalSubgroups G) (hP1 : IsTypeP1 N)
    (hKN : KN ≤ N) (hKN_hall : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N)) :
    Nat.card ↥N = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN := by
  classical
  have hMσle : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
  have hMσHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax
  -- card transfers between `subgroupOf N` and the ambient subgroup
  have hcardNσ : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσle).toEquiv
  have hcardKN : Nat.card ↥(KN.subgroupOf N) = Nat.card ↥KN :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  -- Lagrange inside `↥N`
  have hlagNσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N)
      * ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index = Nat.card ↥N := by
    rw [← hcardNσ]; exact Subgroup.card_mul_index _
  have hlagKN : Nat.card ↥KN * (KN.subgroupOf N).index = Nat.card ↥N := by
    rw [← hcardKN]; exact Subgroup.card_mul_index _
  set m := Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) with hm
  set j := ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index with hjdef
  set a := Nat.card ↥KN with ha
  set j' := (KN.subgroupOf N).index with hj'def
  -- `m`'s primes lie in `σ(N)` (`N_σ` is a Hall `σ`-subgroup)
  have hm_sigma : ∀ p, p ∈ m.primeFactors → p ∈ OddOrder.BG.Ch3.S10.sigma N := hMσHall.1
  -- `a`'s primes avoid `σ(N)` (`κ(N) ⊆ σ(N)′`)
  have ha_sigma : ∀ p, p ∈ a.primeFactors → p ∉ OddOrder.BG.Ch3.S10.sigma N := fun p hp =>
    kappa_subset_sigmaCompl (hKN_hall.1 p (by rw [hcardKN]; exact hp))
  -- `j`'s primes avoid `σ(N)` (`j ∣ (N_σ).index`, a Hall index)
  have hj_div : j ∣ (OddOrder.BG.Ch3.S10.Msigma N).index :=
    Subgroup.relIndex_dvd_index_of_le hMσle
  have hj_sigma : ∀ p, p ∈ j.primeFactors → p ∉ OddOrder.BG.Ch3.S10.sigma N := fun p hp =>
    hMσHall.2 p (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hp).1,
      (Nat.dvd_of_mem_primeFactors hp).trans hj_div, Subgroup.index_ne_zero_of_finite⟩)
  -- `j'`'s primes lie in `σ(N)` (type `P₁`: `κ(N) = π(N) − σ(N)`)
  have hj'_dvd_N : j' ∣ Nat.card ↥N := Subgroup.index_dvd_card _
  have hj'_sigma : ∀ p, p ∈ j'.primeFactors → p ∈ OddOrder.BG.Ch3.S10.sigma N := by
    intro p hp
    have hpprime := (Nat.mem_primeFactors.mp hp).1
    have hp_dvd_N : p ∣ Nat.card ↥N := (Nat.dvd_of_mem_primeFactors hp).trans hj'_dvd_N
    have hp_notκ : p ∉ kappa N := hKN_hall.2 p hp
    rw [hP1.2] at hp_notκ
    by_contra hpσ
    exact hp_notκ ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hp_dvd_N, Nat.card_pos.ne'⟩, hpσ⟩
  -- coprimalities and the `a = j` matching
  have hcop_am : Nat.Coprime a m := Nat.coprime_of_dvd fun p hp hpa hpm =>
    ha_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpa, Nat.card_pos.ne'⟩)
      (hm_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpm, Nat.card_pos.ne'⟩))
  have hcop_jj' : Nat.Coprime j j' := Nat.coprime_of_dvd fun p hp hpj hpj' =>
    hj_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpj, Subgroup.index_ne_zero_of_finite⟩)
      (hj'_sigma p (Nat.mem_primeFactors.mpr ⟨hp, hpj', Subgroup.index_ne_zero_of_finite⟩))
  have ha_dvd_j : a ∣ j := hcop_am.dvd_of_dvd_mul_left (by rw [hlagNσ]; exact ⟨j', hlagKN.symm⟩)
  have hj_dvd_a : j ∣ a := hcop_jj'.dvd_of_dvd_mul_right (by rw [hlagKN]; exact ⟨m, by
    rw [← hlagNσ]; ring⟩)
  have hja : j = a := Nat.dvd_antisymm hj_dvd_a ha_dvd_j
  rw [← hlagNσ, hja]

/-- **BG 14.7, `1 ∉ M̃`** (mmd L3920): the identity is never a "twisted" product `x·x'`
(`x ∈ M_σ^#`, `x' ∈ R(x)`).  If `x·x' = 1` then `x' = x⁻¹`, which has the same order as the
`σ(N)`-element `x`, so `x'` is a `σ(N)`-element; but `x' ∈ R(x)` is a `σ(N)′`-element
(`isPiElement_sigmaCompl_of_mem_Rsub`), and a nonidentity element cannot be both.  Hence each
`𝒞_G(M̃)` avoids `1` and lies in `G^#`, which the density inequality of Theorem 14.7(e) needs. -/
theorem one_not_mem_Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {N : Subgroup G} (hN : N ∈ maximalSubgroups G) :
    (1 : G) ∉ Mtilde hG D N := by
  rintro ⟨x, hxsharp, x', hx'R, hxx'⟩
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hxsharp
  obtain ⟨hxN, hx1⟩ := hxsharp
  have hx'eq : x' = x⁻¹ := (mul_eq_one_iff_inv_eq.mp hxx'.symm).symm
  have hlen : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨N, hN, hxN⟩⟩
  have hπ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hlen ⟨hN, hxN⟩ hx'R
  have hx'1 : x' ≠ 1 := by rw [hx'eq]; exact inv_ne_one.mpr hx1
  have hord : orderOf x' ≠ 1 := fun h => hx'1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hord
  have hordeq : orderOf x' = orderOf x := by rw [hx'eq, orderOf_inv]
  refine hπ p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos x').ne'⟩)
    (OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr ⟨hp,
      (hordeq ▸ hpdvd).trans ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hxN),
      Nat.card_pos.ne'⟩))

/-- **BG Corollary 14.9, the `G#` cover under all-type-`F`** (the covering equality of the
`(8.8.a)` type-I case): when every maximal subgroup is of type `F`, the nonidentity elements of
`G` are exactly the union of the faithful covers `𝒞_G(M̃)` over the maximal subgroups.  The `⊆`
direction is `exists_mem_conjClassSet_Mtilde_of_ne_one` (the discharged form of BG Lemma 14.6),
and `⊇` is `one_not_mem_Mtilde` (`1 ∉ M̃`, so `1 ∉ 𝒞_G(M̃)`).  This is the `cover_nonidentity`
field of `BGTheoremETypeICovering`, modulo replacing the union over all maximals by the union over
conjugacy representatives (`conjClassSet (Mtilde …)` depends only on the conjugacy class via
`Mtilde_conj_smul`). -/
theorem sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hall : ∀ M ∈ maximalSubgroups G, IsTypeF M) :
    sharpSubgroup (⊤ : Subgroup G)
      = ⋃ M ∈ maximalSubgroups G,
          conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) := by
  set D := genuineSigmaDecomposition hG with hD
  ext g
  simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_top, true_and, Set.mem_iUnion₂]
  constructor
  · intro hg1
    obtain ⟨M, hM, hgM⟩ := exists_mem_conjClassSet_Mtilde_of_ne_one hG hall hg1
    exact ⟨M, hM, hgM⟩
  · rintro ⟨M, hM, t, ht, c, hc⟩ rfl
    exact one_not_mem_Mtilde hG D hM ((mul_eq_left.mp (mul_inv_eq_one.mp hc)) ▸ ht)

/-- **BG 14.7, the per-member `σ`-Hall identity** (mmd L4039): for a type-`P₁` member `N` of the
type-`P` family, `|N_σ|·[G : N] = [G : Z]·kᵢ*` where `kᵢ* = |Z ⊓ N_σ|` is the canonical family
factor.  This is the cancellation crux of the density inequality: it turns each
`|𝒞_G(M̃ᵢ)| = (|N_σ| − 1)·[G : N]` summand into `[G : Z]·kᵢ* − [G : N]`, so the `[G : Z]·kᵢ*`
parts cancel against the `𝒞_G(T)` count.  Proof: multiply by `kᵢ = |K_N|` and use
`|N| = |N_σ|·kᵢ` (type `P₁`, `typeP1_card_eq`), `z = kᵢ·kᵢ*` (the swap,
`card_kappaHall_sup_Kstar`), and Lagrange `|N|·[G:N] = |G| = z·[G:Z]`. -/
theorem typeP1_member_Msigma_index_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) (hP1 : IsTypeP1 N) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index
      = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
  classical
  obtain ⟨hNmax, hPN, hZN, KN, hKNN, hKN_hall, hswap, hcanon, hne⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hN
  have hz : Nat.card ↥(K ⊔ Kstar)
      = Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    have h1 := card_kappaHall_sup_Kstar (M := N) (K := KN)
      (Kstar := OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
      hKNN hKN_hall rfl
    rw [← hswap, hcanon] at h1
    exact h1
  have hN_card : Nat.card ↥N
      = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN :=
    typeP1_card_eq hG hNmax hP1 hKNN hKN_hall
  have hlagN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hlagZ : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥KN)) ?_
  calc Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index * Nat.card ↥KN
      = (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * Nat.card ↥KN) * N.index := by ring
    _ = Nat.card ↥N * N.index := by rw [← hN_card]
    _ = Nat.card G := hlagN
    _ = Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index := hlagZ.symm
    _ = (Nat.card ↥KN * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
          * (K ⊔ Kstar).index := by rw [hz]
    _ = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N)
          * Nat.card ↥KN := by ring

/-- **BG 14.7, the per-member index bound** (mmd L4033): each family member `N` has
`2·[G : N] ≤ [G : Z]`, the upper bound on `[G : N]` the density inequality needs (from
`|N| ≥ 2z`, `typeP_family_two_mul_card_le`).  Cancelling `z` from `2z·[G:N] ≤ |N|·[G:N] =
|G| = z·[G:Z]`. -/
theorem typeP_member_two_mul_index_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {N : Subgroup G} (hN : IsZFamilyMember M K N) :
    2 * N.index ≤ (K ⊔ Kstar).index := by
  have h2z : 2 * Nat.card ↥(K ⊔ Kstar) ≤ Nat.card ↥N :=
    typeP_family_two_mul_card_le hG hM hP hKM hK hKstar hU hN
  have hlagN : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hlagZ : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := ↥(K ⊔ Kstar)))
  calc Nat.card ↥(K ⊔ Kstar) * (2 * N.index)
      = (2 * Nat.card ↥(K ⊔ Kstar)) * N.index := by ring
    _ ≤ Nat.card ↥N * N.index := by gcongr
    _ = Nat.card G := hlagN
    _ = Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index := hlagZ.symm

/-- **BG 14.7, the family has `≥ 2` members** (mmd L3993, "`n ≥ 1`"): the type-`P` family
`{M} ∪ {neighbours}` has at least two members — `M` itself and a neighbour `N ∈ 𝓜(N_G(X))` for a
line `X ∈ ℰ_p¹(K)` (`p ∣ |K|`), which is nonconjugate to `M` (`exists_typeP_partner`).  This is
the `n ≥ 1` the density inequality needs for `(n − 1)/2z ≥ 0`. -/
theorem ZFamilyFinset_one_lt_card [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    1 < (ZFamilyFinset M K).card := by
  classical
  have hPe := hP
  obtain ⟨p, hpκ⟩ := hPe
  have hpprime := hpκ.1
  obtain ⟨P, hPelem, hPM, -⟩ := hpκ.2.2
  have hpcardP : Nat.card ↥P = p := by obtain ⟨_, hc⟩ := hPelem; rwa [pow_one] at hc
  have hpK : p ∣ Nat.card ↥K := by
    have hlag : Nat.card ↥K * (K.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact Subgroup.card_mul_index (K.subgroupOf M)
    have hpM : p ∣ Nat.card ↥M := hpcardP ▸ Subgroup.card_dvd_of_le hPM
    have hpidx : ¬ p ∣ (K.subgroupOf M).index := fun hd =>
      hK.2 p (Nat.mem_primeFactors.mpr ⟨hpprime, hd, Subgroup.index_ne_zero_of_finite⟩) hpκ
    exact (hpprime.dvd_mul.mp (hlag.symm ▸ hpM)).resolve_right hpidx
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, -, -, -, -⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNfam : IsZFamilyMember M K N :=
    Or.inr ⟨p, Subgroup.zpowers (x : G), hpprime, hXelem, hXK, hNmem⟩
  have hMN : M ≠ N := fun h => hnc (h ▸ IsConjugateSubgroup.refl M)
  exact Finset.one_lt_card.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl), N,
    mem_ZFamilyFinset.mpr hNfam, hMN⟩

/-- The identity is conjugacy-closed: if `1 ∉ A` then `1 ∉ 𝒞_G(A)` (a conjugate `g·t·g⁻¹ = 1`
forces `t = 1`).  Used to place each density piece `𝒞_G(T)`, `𝒞_G(M̃ᵢ)` inside `G^#`. -/
theorem one_not_mem_conjClassSet {A : Set G} (h : (1 : G) ∉ A) :
    (1 : G) ∉ conjClassSet A := by
  rintro ⟨t, ht, g, hg⟩
  rw [(MulAut.conj_apply g t).symm, ← map_one (MulAut.conj g)] at hg
  exact h ((MulAut.conj g).injective hg ▸ ht)

/-- **BG 14.7, the density pieces fit in `G^#`** (mmd L4035): the conjugacy saturations `𝒞_G(T)`
and `{𝒞_G(M̃ᵢ)}_{i}` over the type-`P` family are pairwise disjoint subsets of `G^# = G − {1}`, so
their cardinalities sum to at most `|G| − 1`.  Disjointness: `𝒞_G(T) ⊥ 𝒞_G(M̃ᵢ)`
(`conjClassSet_T_Mtilde_disjoint`, Lemma 14.6) and `𝒞_G(M̃ᵢ) ⊥ 𝒞_G(M̃ⱼ)`
(`conjClassSet_Mtilde_disjoint`, Lemma 14.5(b), via pairwise nonconjugacy of the family).
Membership in `G^#`: `1 ∉ T` (`1 ∈ Kᵢ*`) and `1 ∉ M̃ᵢ` (`one_not_mem_Mtilde`).  This is the
upper bound `∑ |𝒞_G(·)| ≤ |G^#|` of the density inequality of Theorem 14.7(e). -/
theorem density_pieces_ncard_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (conjClassSet (((K ⊔ Kstar : Subgroup G) : Set G) \
        ⋃ N ∈ ZFamilyFinset M K,
          (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))).ncard
      + (∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard)
      ≤ Nat.card G - 1 := by
  classical
  set Tset := ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) with hTset
  set A := conjClassSet Tset with hA
  set U := ⋃ N ∈ (↑(ZFamilyFinset M K) : Set (Subgroup G)), conjClassSet (Mtilde hG D N) with hU'
  -- `U.ncard = ∑ |𝒞_G(M̃ᵢ)|`
  have hpair : (↑(ZFamilyFinset M K) : Set (Subgroup G)).PairwiseDisjoint
      (fun N => conjClassSet (Mtilde hG D N)) := by
    intro N₁ hN₁ N₂ hN₂ hne
    refine conjClassSet_Mtilde_disjoint hG D
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN₁)).1
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN₂)).1 ?_
    exact typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN₁) (mem_ZFamilyFinset.mp hN₂) hne
  have hUcard : U.ncard = ∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard := by
    rw [hU', Set.Finite.ncard_biUnion (ZFamilyFinset M K).finite_toSet
      (fun N _ => Set.toFinite _) hpair, finsum_mem_coe_finset]
  -- all pieces avoid `1`
  have h1T : (1 : G) ∉ Tset := fun h =>
    (Set.mem_sdiff _ |>.mp h).2 (Set.mem_iUnion₂.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl),
      SetLike.mem_coe.mpr (Subgroup.one_mem _)⟩)
  have h1A : (1 : G) ∉ A := one_not_mem_conjClassSet h1T
  have h1U : (1 : G) ∉ U := by
    rw [hU', Set.mem_iUnion₂]; rintro ⟨N, hN, hzN⟩
    exact one_not_mem_conjClassSet (one_not_mem_Mtilde hG D
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).1) hzN
  -- `A` disjoint from `U`
  have hAU : Disjoint A U := by
    rw [Set.disjoint_left]
    rintro z hzA hzU
    rw [hU', Set.mem_iUnion₂] at hzU
    obtain ⟨N, hN, hzN⟩ := hzU
    exact Set.disjoint_left.mp (conjClassSet_T_Mtilde_disjoint hG D hM hP hKM hK hKstar hU
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).1) hzA hzN
  -- `A ∪ U ⊆ G^#`
  have hsub : A ∪ U ⊆ {g : G | g ≠ 1} := by
    rintro z (hz | hz)
    · exact fun h => h1A (h ▸ hz)
    · exact fun h => h1U (h ▸ hz)
  have hWcard : ({g : G | g ≠ 1} : Set G).ncard = Nat.card G - 1 := by
    have hWeq : {g : G | g ≠ 1} = (Set.univ : Set G) \ {1} := by
      ext g; simp [Set.mem_sdiff]
    rw [hWeq, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (Set.mem_univ 1)), Set.ncard_univ,
      Set.ncard_singleton]
  calc A.ncard + ∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard
      = A.ncard + U.ncard := by rw [hUcard]
    _ = (A ∪ U).ncard := (Set.ncard_union_eq hAU).symm
    _ ≤ ({g : G | g ≠ 1} : Set G).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card G - 1 := hWcard

/-- **BG Theorem 14.7, the density inequality** (mmd L4031-4045): some member of the type-`P`
family `{M} ∪ {neighbours}` has type `P₂`.  If every member were type `P₁`, the disjoint conjugacy
pieces `𝒞_G(T)` and `{𝒞_G(M̃ᵢ)}` would already cover `G^#`:
`|G^#| ≥ |𝒞_G(T)| + ∑ |𝒞_G(M̃ᵢ)| = |G| + n·[G:Z] − ∑ [G:Mᵢ] ≥ |G| + (n−1)·[G:Z]/… ≥ |G|`,
contradicting `|G^#| = |G| − 1`.  The `∑ [G:Z]·kᵢ*` parts cancel between the two counts
(`typeP1_member_Msigma_index_eq`); the bound uses `[G:Mᵢ] ≤ [G:Z]/2` (`|Mᵢ| ≥ 2z`) and `n ≥ 1`
(a neighbour exists).  Entirely a `ℕ` computation closed by `omega`. -/
theorem exists_typeP2_member [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ N ∈ ZFamilyFinset M K, IsTypeP2 N := by
  classical
  by_contra hcon
  push Not at hcon
  have hallP1 : ∀ N ∈ ZFamilyFinset M K, IsTypeP1 N := fun N hN =>
    (isTypeP_iff_isTypeP1_or_isTypeP2.mp
      (typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN)).2.1).resolve_right
      (hcon N hN)
  -- lemma instances (explicit `T`), then fold `T`
  have hT_count := typeP_family_conjClass_T_count hG hM hP hKM hK hKstar hU
  have hT_card := typeP_family_T_count hG hM hP hKM hK hKstar hU
  have hbound := density_pieces_ncard_le hG D hM hP hKM hK hKstar hU
  have hcardlt := ZFamilyFinset_one_lt_card hG hM hP hKM hK hKstar hU
  set Tset := ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) with hTset
  have hzcard : Nat.card ↥(K ⊔ Kstar) * (K ⊔ Kstar).index = Nat.card G :=
    Subgroup.card_mul_index _
  -- per-member `M̃` additive identity and its sum
  have hmem_add : ∀ N ∈ ZFamilyFinset M K,
      (conjClassSet (Mtilde hG D N)).ncard + N.index
        = (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    intro N hN
    have hNmax := (typeP_family_member_data hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN)).1
    have hmem_id := typeP1_member_Msigma_index_eq hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp hN) (hallP1 N hN)
    rw [sigmaConjugacySaturation_Mtilde_ncard hG D hNmax, Nat.sub_one_mul]
    have hge : N.index ≤ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma N) * N.index :=
      Nat.le_mul_of_pos_left _ Nat.card_pos
    omega
  have hMtilde_sum : (∑ N ∈ ZFamilyFinset M K, (conjClassSet (Mtilde hG D N)).ncard)
      + (∑ N ∈ ZFamilyFinset M K, N.index)
      = ∑ N ∈ ZFamilyFinset M K,
          (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hmem_add
  -- `T` additive (multiply the `|T|` count by `[G:Z]`)
  have hmul : Tset.ncard * (K ⊔ Kstar).index
      + (∑ N ∈ ZFamilyFinset M K,
          Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) * (K ⊔ Kstar).index)
      + (K ⊔ Kstar).index
      = Nat.card G + (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
    have h := congrArg (· * (K ⊔ Kstar).index) hT_card
    simp only [add_mul, one_mul, Finset.sum_mul] at h
    rw [hzcard] at h
    exact h
  have hPcomm : (∑ N ∈ ZFamilyFinset M K,
        (K ⊔ Kstar).index * Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N))
      = ∑ N ∈ ZFamilyFinset M K,
        Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) * (K ⊔ Kstar).index :=
    Finset.sum_congr rfl (fun N _ => mul_comm _ _)
  -- key inequality `∑ [G:Mᵢ] ≤ (𝓕.card − 1)·[G:Z]`
  have hkey : (∑ N ∈ ZFamilyFinset M K, N.index)
      ≤ ((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index := by
    have h2sum : 2 * (∑ N ∈ ZFamilyFinset M K, N.index)
        ≤ (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
      rw [Finset.mul_sum]
      calc (∑ N ∈ ZFamilyFinset M K, 2 * N.index)
          ≤ ∑ _N ∈ ZFamilyFinset M K, (K ⊔ Kstar).index :=
            Finset.sum_le_sum (fun N hN => typeP_member_two_mul_index_le hG hM hP hKM hK hKstar hU
              (mem_ZFamilyFinset.mp hN))
        _ = (ZFamilyFinset M K).card * (K ⊔ Kstar).index := by
            rw [Finset.sum_const, smul_eq_mul]
    have hc2 : (ZFamilyFinset M K).card ≤ 2 * ((ZFamilyFinset M K).card - 1) := by omega
    have hstep : (ZFamilyFinset M K).card * (K ⊔ Kstar).index
        ≤ 2 * (((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index) := by
      rw [← mul_assoc]; exact mul_le_mul_right' hc2 _
    omega
  -- expansion fact relating `𝓕.card·[G:Z]` and `(𝓕.card−1)·[G:Z]`
  have hexp : (ZFamilyFinset M K).card * (K ⊔ Kstar).index
      = ((ZFamilyFinset M K).card - 1) * (K ⊔ Kstar).index + (K ⊔ Kstar).index := by
    have hle : (K ⊔ Kstar).index ≤ (ZFamilyFinset M K).card * (K ⊔ Kstar).index :=
      Nat.le_mul_of_pos_left _ (by omega)
    rw [Nat.sub_one_mul]; omega
  have hgpos : 1 ≤ Nat.card G := Nat.card_pos
  omega

/-- **A `πᶜ`-subgroup of an internal direct product `Z = A × B` (`A` a `πᶜ`-group, `B` a
`π`-group) lies in the left factor `A`.**  Subgroup generalisation of
`isPiElementCompl_mem_left_of_commute`: `A.subgroupOf Z` is the normal Hall `πᶜ`-subgroup of `Z`,
so any `πᶜ`-subgroup `L ≤ Z` lies in it (`isPiGroup_le_of_normal_isHallSubgroup`).  In the `n = 1`
collapse of Theorem 14.7, `A = Kᵢ` (the Hall `κ(Mᵢ) ⊆ σ(Mᵢ)′`-subgroup), `B = Kᵢ*` (the
`σ(Mᵢ)`-part), and `L = Kⱼ*` (a `σ(Mᵢ)′`-group since `σ(Mⱼ) ∩ σ(Mᵢ) = ∅`), forcing `Kⱼ* ≤ Kᵢ`. -/
theorem isPiSubgroup_le_left_of_commute [Finite G] {A B Z L : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    (hLZ : L ≤ Z) (hLπc : Subgroup.IsPiSubgroup πᶜ L) : L ≤ A := by
  classical
  have hAZ : A ≤ Z := by rw [hswap]; exact le_sup_left
  have hcomm : ∀ a ∈ A, ∀ c ∈ B, Commute a c := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp (hcent hc) a ha
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    apply Nat.coprime_of_dvd
    intro p hp hpA hpB
    exact (hAπc p (Nat.mem_primeFactors.mpr ⟨hp, hpA, Nat.card_pos.ne'⟩))
      (hBπ p (Nat.mem_primeFactors.mpr ⟨hp, hpB, Nat.card_pos.ne'⟩))
  have hdisj : A ⊓ B = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hnorm : Z ≤ Subgroup.normalizer (A : Set G) := by
    rw [hswap]; exact (sup_le_normalizer_inf_of_commute hcent).trans inf_le_left
  haveI hAnZ : (A.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAZ).mpr hnorm
  have hZcard : Nat.card ↥Z = Nat.card ↥A * Nat.card ↥B := by
    rw [hswap]; exact card_sup_of_commute_of_disjoint hcomm hdisj
  have hcardSub : Nat.card ↥(A.subgroupOf Z) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hidx : (A.subgroupOf Z).index = Nat.card ↥B := by
    have hl := Subgroup.card_mul_index (A.subgroupOf Z)
    rw [hcardSub, hZcard] at hl
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hl
  have hHall : Ch03.IsHallSubgroup πᶜ (A.subgroupOf Z) := by
    refine ⟨fun p hp => ?_, fun p hp hpc => ?_⟩
    · rw [hcardSub] at hp; exact hAπc p hp
    · exact hpc (hBπ p (by rwa [hidx] at hp))
  have hLsub : L.subgroupOf Z ≤ A.subgroupOf Z := by
    refine OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall (fun p hp => ?_)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv] at hp
    exact hLπc p hp
  intro x hx
  have hmem : (⟨x, hLZ hx⟩ : ↥Z) ∈ L.subgroupOf Z := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hLsub hmem)

/-- **BG Theorem 14.7, the `n = 1` collapse** (mmd L4047): the type-`P` family `{M} ∪ {neighbours}`
has exactly two members.  By the density inequality some member `Mᵢ` is type `P₂`, so its Hall
`κ(Mᵢ)`-subgroup `Kᵢ` has prime order `q` (Proposition 14.2(g)).  In the swap `Z = Kᵢ × Kᵢ*`, `Kᵢ`
is the normal Hall `σ(Mᵢ)′`-subgroup; every other member `Mⱼ` has `Kⱼ* = Z ⊓ M_{jσ}` a nontrivial
`σ(Mᵢ)′`-subgroup of `Z` (`σ(Mⱼ) ∩ σ(Mᵢ) = ∅` by Theorem 13.9), hence `Kⱼ* ≤ Kᵢ`
(`isPiSubgroup_le_left_of_commute`), and `Kⱼ* = Kᵢ` since `|Kᵢ| = q` is prime.  But the `Kⱼ*` are
pairwise disjoint (`typeP_family_Kstar_disjoint`), so two distinct neighbours would give
`Kᵢ = Kⱼ* ⊓ Kₗ* = 1`, contradicting `q ≥ 2`.  Thus at most one neighbour, i.e. `|family| = 2`. -/
theorem family_card_eq_two [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    (ZFamilyFinset M K).card = 2 := by
  classical
  refine le_antisymm ?_ (ZFamilyFinset_one_lt_card hG hM hP hKM hK hKstar hU)
  obtain ⟨Mi, hMi𝓕, hMiP2⟩ := exists_typeP2_member hG D hM hP hKM hK hKstar hU
  obtain ⟨hMimax, hMiP, hZMi, KNi, hKNiMi, hKNi, hswapi, hcanoni, hnei⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hMi𝓕)
  -- `|KNi| = q` is prime (Proposition 14.2(g))
  haveI : IsSolvable ↥Mi := hG.solvable_of_mem_maximalSubgroups hMimax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mi)
    ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
  have hUeq : (U'.map Mi.subtype).subgroupOf Mi = U' :=
    Subgroup.comap_map_eq_self_of_injective Mi.subtype_injective U'
  have hUi : Ch03.IsHallSubgroup ((kappa Mi ∪ OddOrder.BG.Ch3.S10.sigma Mi)ᶜ)
      ((U'.map Mi.subtype).subgroupOf Mi) := by rw [hUeq]; exact hU'
  obtain ⟨q, hq, hqcard, -⟩ :=
    ((typeP_structure hG hMimax hMiP hKNiMi hKNi rfl hUi).2.2.2.2.1 hMiP2).2
  have hKNine : KNi ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hqcard; exact hq.ne_one hqcard.symm
  -- the `σ(Mᵢ)′`-Hall data of the swap `Z = KNi × Kᵢ*` for `isPiSubgroup_le_left_of_commute`
  have hswapMi : K ⊔ Kstar = KNi ⊔ ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi) :=
    hswapi.trans (by rw [hcanoni])
  have hcentMi : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi
      ≤ Subgroup.centralizer (KNi : Set G) := hcanoni ▸ inf_le_right
  have hAπc : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)ᶜ KNi :=
    kappaHall_isPiSubgroup_sigmaCompl hKNiMi hKNi
  have hBπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)
      ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mi) := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mi p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1,
        (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right),
        Nat.card_pos.ne'⟩)
  -- every member `≠ Mᵢ` has its canonical factor equal to `KNi`
  have hKstarEq : ∀ N ∈ (ZFamilyFinset M K).erase Mi,
      (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N = KNi := by
    intro N hNe
    have hN𝓕 := Finset.mem_of_mem_erase hNe
    have hNneMi : N ≠ Mi := Finset.ne_of_mem_erase hNe
    obtain ⟨hNmax, hNP, -, KNj, -, -, -, hcanonj, hnej⟩ :=
      typeP_family_member_data hG hM hP hKM hK hKstar hU (mem_ZFamilyFinset.mp hN𝓕)
    have hnej' : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≠ ⊥ := hcanonj ▸ hnej
    have hdisjσ : Disjoint (OddOrder.BG.Ch3.S10.sigma Mi) (OddOrder.BG.Ch3.S10.sigma N) :=
      sigma_disjoint_of_nonconjugate hG hMimax hNmax
        (typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU
          (mem_ZFamilyFinset.mp hMi𝓕) (mem_ZFamilyFinset.mp hN𝓕) (Ne.symm hNneMi))
    have hLπc : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mi)ᶜ
        ((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) := fun p hp => by
      have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hp).1,
            (Nat.dvd_of_mem_primeFactors hp).trans (Subgroup.card_dvd_of_le inf_le_right),
            Nat.card_pos.ne'⟩)
      exact fun hpσMi => Set.disjoint_left.mp hdisjσ hpσMi hpσN
    have hle : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N ≤ KNi :=
      isPiSubgroup_le_left_of_commute hswapMi hcentMi hAπc hBπ inf_le_left hLπc
    -- prime-order `KNi`: a nontrivial subgroup is all of it
    have hdvd : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ∣ q := by
      rw [← hqcard]; exact Subgroup.card_dvd_of_le hle
    have hne1 : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) ≠ 1 :=
      fun h => hnej' (Subgroup.eq_bot_of_card_eq _ h)
    have hcardeq : Nat.card ↥((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N) = Nat.card ↥KNi := by
      rw [hqcard]; exact (hq.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
    exact Subgroup.eq_of_le_of_card_ge hle hcardeq.ge
  -- at most one member is `≠ Mᵢ`
  have herase_le : ((ZFamilyFinset M K).erase Mi).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have hdisj := typeP_family_Kstar_disjoint hG hM hP hKM hK hKstar hU
      (mem_ZFamilyFinset.mp (Finset.mem_of_mem_erase ha))
      (mem_ZFamilyFinset.mp (Finset.mem_of_mem_erase hb)) hab
    rw [hKstarEq a ha, hKstarEq b hb, inf_idem] at hdisj
    rw [hdisj, Subgroup.card_bot] at hqcard
    exact hq.ne_one hqcard.symm
  have hcard_erase := Finset.card_erase_of_mem hMi𝓕
  omega

/-- **BG Theorem 14.7, the unique partner `M*`** (mmd L4047): since the type-`P` family has exactly
two members (`family_card_eq_two`) and `M` is one of them, there is a unique other member `M*`, the
nonconjugate partner of Theorem 14.7.  It is a type-`P` maximal subgroup containing `Z = K ⊔ K*`,
nonconjugate to `M`. -/
theorem exists_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃ Mstar : Subgroup G, Mstar ≠ M ∧ IsZFamilyMember M K Mstar ∧
      ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar := by
  classical
  obtain ⟨a, b, hab, hfam⟩ :=
    Finset.card_eq_two.mp (family_card_eq_two hG D hM hP hKM hK hKstar hU)
  have hMfam : M ∈ ZFamilyFinset M K := mem_ZFamilyFinset.mpr (Or.inl rfl)
  rw [hfam, Finset.mem_insert, Finset.mem_singleton] at hMfam
  rcases hMfam with hMa | hMb
  · refine ⟨b, by rw [hMa]; exact Ne.symm hab,
      mem_ZFamilyFinset.mp (by rw [hfam]; simp), fun N hN => ?_⟩
    have hN' : N ∈ ({a, b} : Finset (Subgroup G)) := hfam ▸ mem_ZFamilyFinset.mpr hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN'
    exact hN'.imp (fun h => h.trans hMa.symm) id
  · refine ⟨a, by rw [hMb]; exact hab,
      mem_ZFamilyFinset.mp (by rw [hfam]; simp), fun N hN => ?_⟩
    have hN' : N ∈ ({a, b} : Finset (Subgroup G)) := hfam ▸ mem_ZFamilyFinset.mpr hN
    rw [Finset.mem_insert, Finset.mem_singleton] at hN'
    exact hN'.elim (fun h => Or.inr h) (fun h => Or.inl (h.trans hMb.symm))

/-- **BG Theorem 14.7(f), the type-`P₂` dichotomy** (mmd L4047): for the partner `M*` (so every
family member is `M` or `M*`), one of `M`, `M*` is type `P₂`.  Immediate from the density
inequality (`exists_typeP2_member`): the type-`P₂` member it produces is `M` or `M*`. -/
theorem isTypeP2_or_isTypeP2_partner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    IsTypeP2 M ∨ IsTypeP2 Mstar := by
  obtain ⟨N, hN𝓕, hNP2⟩ := exists_typeP2_member hG D hM hP hKM hK hKstar hU
  rcases hpart N (mem_ZFamilyFinset.mp hN𝓕) with h | h
  · subst h; exact Or.inl hNP2
  · subst h; exact Or.inr hNP2

/-- **BG Theorem 14.7, `π(K) ⊆ σ(M*)`** (mmd L3987): every prime `p` dividing `|K|` lies in
`σ(M*)`, for the partner `M*`.  For a line `X ∈ ℰ_p¹(K)`, the maximal subgroup over `N_G(X)` is a
type-`P` family member nonconjugate to `M` (`exists_typeP_partner`), hence `= M*` (the only other
member), and `X ≤ M*_σ` gives `p ∈ σ(M*)`.  This is the half forcing `K ≤ M*_σ` in the partner
structure `Z ⊓ M*_σ = K`. -/
theorem kappaHall_primes_subset_sigma_partner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card ↥K) :
    p ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  obtain ⟨N, hNmem, hnc, -, hXNσ, -, -⟩ :=
    exists_typeP_partner hG hM hP hKM hK hKstar hU hXelem hXK
  have hNfam : IsZFamilyMember M K N :=
    Or.inr ⟨p, Subgroup.zpowers (x : G), hp, hXelem, hXK, hNmem⟩
  have hNM : N ≠ M :=
    fun h => hnc (h ▸ (⟨1, by rw [map_one, one_smul]⟩ : IsConjugateSubgroup M M))
  have hNMstar : N = Mstar := (hpart N hNfam).resolve_left hNM
  rw [← hNMstar]
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
    ⟨hp, (dvd_of_eq hXcard.symm).trans (Subgroup.card_dvd_of_le hXNσ), Nat.card_pos.ne'⟩)

/-- **BG Theorem 14.7, the partner canonical factor** (mmd L3995): `Z ⊓ M*_σ = K`.  In the swap
`Z = M*'s K* × M*'s κ-Hall`, the partner's canonical factor `Z ⊓ M*_σ` equals `K` (the original
`M`'s Hall `κ`-subgroup).  Two inclusions: `Z ⊓ M*_σ` is a `σ(M)′`-subgroup of the direct product
`Z = K × K*` (`σ(M*) ∩ σ(M) = ∅`), so it lies in the `σ(M)′`-Hall factor `K`
(`isPiSubgroup_le_left_of_commute`); conversely `K ≤ M*_σ` because every prime of `K` lies in
`σ(M*)` (`kappaHall_primes_subset_sigma_partner`).  This is the structural fact that turns the
family's `T = Z − ⋃ Kᵢ*` into `Ẑ = Z − (K ∪ K*)`. -/
theorem partner_canonical_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = K := by
  classical
  have hMstarmax : Mstar ∈ maximalSubgroups G :=
    (typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem).1
  have hZMstar : K ⊔ Kstar ≤ Mstar :=
    (typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem).2.2.1
  have hnc : ¬ IsConjugateSubgroup M Mstar :=
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne)
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG hM hMstarmax hnc
  refine le_antisymm ?_ (le_inf le_sup_left ?_)
  · -- `Z ⊓ M*_σ ≤ K`: it is a `σ(M)′`-subgroup of `Z = K × K*`
    refine isPiSubgroup_le_left_of_commute (π := OddOrder.BG.Ch3.S10.sigma M) rfl
      (hKstar ▸ inf_le_right) (kappaHall_isPiSubgroup_sigmaCompl hKM hK) (fun q hq => ?_)
      inf_le_left (fun q hq => ?_)
    · exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
          (Subgroup.card_dvd_of_le (hKstar.le.trans inf_le_left)), Nat.card_pos.ne'⟩)
    · have hqσMstar : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar q (Nat.mem_primeFactors.mpr
          ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
            (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      exact fun hqσM => Set.disjoint_left.mp hσdisj hqσM hqσMstar
  · -- `K ≤ M*_σ`: every prime of `K` lies in `σ(M*)`
    refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarmax) (le_sup_left.trans hZMstar) (fun q hq => ?_)
    exact kappaHall_primes_subset_sigma_partner hG hM hP hKM hK hKstar hU hpart
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)

/-- **BG Theorem 14.7(e), the family `Z ⊓ N_σ` collapse** (mmd L4051): for the type-`P` family
`{M, M*}` (recorded by `hpart`), the union of the canonical factors collapses to `K ∪ K*`,
`⋃_{N ∈ 𝓕} (Z ⊓ N_σ) = K ∪ K*`, since `Z ⊓ M_σ = K*` (`typeP_self_member`) and `Z ⊓ M*_σ = K`
(`partner_canonical_eq`).  Factored out of `typeP_zTilde_isTI`; reused by the `> ½|G|` density
count `typeP_zTilde_conjClass_gt_half`, where it identifies `Ẑ = Z − (K ∪ K*)` with the family
TI-set `T = Z − ⋃_{N} (Z ⊓ N_σ)`. -/
theorem family_inf_msigma_union_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    (⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G))
      = ((K : Set G) ∪ (Kstar : Set G)) := by
  classical
  have hcanonM : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar :=
    (typeP_self_member hG hM hP hKM hK hKstar hU).1
  have hcanonMstar : (K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = K :=
    partner_canonical_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  apply Set.Subset.antisymm
  · rintro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨N, hN, hxN⟩ := hx
    rcases hpart N (mem_ZFamilyFinset.mp hN) with rfl | rfl
    · rw [hcanonM] at hxN; exact Or.inr hxN
    · rw [hcanonMstar] at hxN; exact Or.inl hxN
  · rintro x (hxK | hxKstar)
    · exact Set.mem_iUnion₂.mpr ⟨Mstar, mem_ZFamilyFinset.mpr hMstarmem,
        by rw [hcanonMstar]; exact hxK⟩
    · exact Set.mem_iUnion₂.mpr ⟨M, mem_ZFamilyFinset.mpr (Or.inl rfl),
        by rw [hcanonM]; exact hxKstar⟩

/-- **BG Theorem 14.7(e), `Ẑ` is a TI-subset** (mmd L4051): with the family `{M, M*}`, the
union `⋃_{N} (Z ⊓ N_σ)` collapses to `K ∪ K*` (`family_inf_msigma_union_eq`), so the family TI-set
`T = Z − ⋃ (Z ⊓ N_σ)` equals `Ẑ = Z − (K ∪ K*)`.  Hence `Ẑ` inherits the TI property from
`typeP_family_T_isTI`.  A conjunct of the `∃! Mstar`. -/
theorem typeP_zTilde_isTI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    OddOrder.GroupTheory.IsTISubset (zTilde K Kstar) (K ⊔ Kstar) := by
  classical
  have hunion := family_inf_msigma_union_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hzeq : zTilde K Kstar = ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    simp only [zTilde]; rw [hunion]
  rw [hzeq]
  exact typeP_family_T_isTI hG hM hP hKM hK hKstar hU

/-- Pure `ℕ` identity for the `|Ẑ|` count: `k·l − (k + l − 1) = (k − 1)(l − 1)` for `k, l ≥ 1`. -/
private theorem nat_mul_sub_kl_identity {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    k * l - (k + l - 1) = (k - 1) * (l - 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hl
  have h1 : (1 + a) * (1 + b) = a * b + a + b + 1 := by ring
  have h2 : (1 + a - 1) * (1 + b - 1) = a * b := by simp
  omega

/-- `1 ∉ Ẑ`: the identity lies in `K ≤ K ⊔ K*`, hence in the removed set `K ∪ K*`.  So
`sharpSubgroup Ẑ = Ẑ` and `𝒞_G(Ẑ^#) ⊆ G^#` — a prerequisite for the NonType-I `G^#` cover. -/
theorem one_not_mem_zTilde (K Kstar : Subgroup G) : (1 : G) ∉ zTilde K Kstar := by
  rw [zTilde, Set.mem_sdiff, not_and_or, not_not]
  exact Or.inr (Set.mem_union_left _ (SetLike.mem_coe.mpr K.one_mem))

/-- **`Ẑ` is symmetric in its two factors**: `zTilde K K* = zTilde K* K` (both `K ⊔ K*` and
`K ∪ K*` are symmetric).  Used for the partner side, where the swap exchanges `K ↔ K*`. -/
theorem zTilde_comm (K Kstar : Subgroup G) : zTilde K Kstar = zTilde Kstar K := by
  rw [zTilde, zTilde, sup_comm, Set.union_comm]

/-- **`Ẑ` is `G`-conjugation equivariant**: `(zTilde K K*)^g = zTilde (K^g) (K*^g)`.  Conjugation is
a set bijection commuting with `\`, `∪`, and `⊔` (`Subgroup.smul_sup`), so it distributes through
the `zTilde = (K ⊔ K*) ∖ (K ∪ K*)` definition.  Lets a `zTilde` of a conjugate type-`P` maximal be
identified (up to `conjClassSet`) with a fixed `Ẑ`. -/
theorem zTilde_conj_smul (g : G) (K Kstar : Subgroup G) :
    MulAut.conj g • zTilde K Kstar
      = zTilde (MulAut.conj g • K) (MulAut.conj g • Kstar) := by
  rw [zTilde, zTilde, Set.smul_set_sdiff, Set.smul_set_union,
    ← Subgroup.coe_pointwise_smul, ← Subgroup.coe_pointwise_smul,
    ← Subgroup.coe_pointwise_smul, Subgroup.smul_sup]

/-- **`𝒞_G` is invariant under conjugating the underlying set**: `𝒞_G(S^g) = 𝒞_G(S)` (conjugation
permutes `G`-conjugacy classes, fixing their union). -/
theorem conjClassSet_conj_smul (g : G) (S : Set G) :
    conjClassSet (MulAut.conj g • S) = conjClassSet S := by
  ext y
  simp only [OddOrder.GroupTheory.mem_conjClassSet]
  constructor
  · rintro ⟨t, ht, b, rfl⟩
    rw [Set.mem_smul_set] at ht
    obtain ⟨s, hs, hst⟩ := ht
    refine ⟨s, hs, b * g, ?_⟩
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]; group
  · rintro ⟨s, hs, b, rfl⟩
    refine ⟨MulAut.conj g • s, Set.smul_mem_smul_set hs, b * g⁻¹, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]; group

/-- **`𝒞_G(Ẑ)` only depends on the `G`-conjugacy class of `(K, K*)`**: conjugating both factors by
`g` leaves `𝒞_G(zTilde K K*)` unchanged.  This is the fix-`W` step — a `zTilde` of a conjugate
type-`P` maximal has the same `conjClassSet` as the reference `Ẑ`. -/
theorem conjClassSet_zTilde_conj_eq (g : G) (K Kstar : Subgroup G) :
    conjClassSet (zTilde (MulAut.conj g • K) (MulAut.conj g • Kstar))
      = conjClassSet (zTilde K Kstar) := by
  rw [← zTilde_conj_smul, conjClassSet_conj_smul]

/-- **Algebraic core of the κ→Ẑ identification** (the final step of BG `mFT_partition` part 2):
a product `y · y'` of a nonidentity `K*`-element `y` and a nonidentity `K`-element `y'` lies in
`Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`, provided `K ⊓ K* = ⊥`.  Membership in `K ⊔ K*` is immediate; `y·y' ∉ K`
because then `y = (y·y')·y'⁻¹ ∈ K ⊓ K* = ⊥` contradicts `y ≠ 1`, and dually `y·y' ∉ K*`.  The deep
part of κ→Ẑ (placing the σ-part `y` in `K* = C_{M_σ}(K)` via `Z = K ⊔ K*` cyclic, and the
`κ`-element `y'` in the Hall `K`) wraps this core. -/
theorem mem_zTilde_of_mul {K Kstar : Subgroup G} (htri : K ⊓ Kstar = ⊥)
    {y y' : G} (hy : y ∈ Kstar) (hy1 : y ≠ 1) (hy' : y' ∈ K) (hy'1 : y' ≠ 1) :
    y * y' ∈ zTilde K Kstar := by
  rw [zTilde, Set.mem_sdiff]
  refine ⟨(K ⊔ Kstar).mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hy'), ?_⟩
  rw [Set.mem_union, not_or]
  refine ⟨fun hmem => hy1 ?_, fun hmem => hy'1 ?_⟩
  · have hyK : y ∈ K := by
      have h := K.mul_mem (SetLike.mem_coe.mp hmem) (K.inv_mem hy')
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h
    have h := Subgroup.mem_inf.mpr ⟨hyK, hy⟩
    rwa [htri, Subgroup.mem_bot] at h
  · have hy'Ks : y' ∈ Kstar := by
      have h := Kstar.mul_mem (Kstar.inv_mem hy) (SetLike.mem_coe.mp hmem)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h
    have h := Subgroup.mem_inf.mpr ⟨hy', hy'Ks⟩
    rwa [htri, Subgroup.mem_bot] at h

/-- **`y ∈ C_G(K)` from `y ∈ Z = K ⊔ K*` with `Z` cyclic** (the `cKZ` step of κ→Ẑ): since the
join `K ⊔ K*` is cyclic — hence abelian — every element of it centralizes `K`.  Combined with
`y ∈ M_σ`, this places the σ-part `y` in `K* = M_σ ⊓ C_G(K)`. -/
theorem mem_centralizer_of_mem_sup_isCyclic {K Kstar : Subgroup G}
    (hcyc : IsCyclic ↥(K ⊔ Kstar)) {y : G} (hyZ : y ∈ K ⊔ Kstar) :
    y ∈ Subgroup.centralizer (K : Set G) := by
  haveI := hcyc
  letI : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkZ : k ∈ K ⊔ Kstar := Subgroup.mem_sup_left (SetLike.mem_coe.mp hk)
  have hcomm : (⟨k, hkZ⟩ : ↥(K ⊔ Kstar)) * ⟨y, hyZ⟩ = ⟨y, hyZ⟩ * ⟨k, hkZ⟩ := mul_comm _ _
  have h := congrArg (Subgroup.subtype (K ⊔ Kstar)) hcomm
  simpa using h

/-- **BG Theorem 14.7, `|Ẑ| = (k − 1)(k* − 1)`** (mmd L4051): the TI-set `Ẑ = Z − (K ∪ K*)` has
`(|K| − 1)(|K*| − 1)` elements.  `|Z| = |K|·|K*|` (`card_kappaHall_sup_Kstar`), `K ∩ K* = 1`
(`kappaHall_inf_Kstar_eq_bot`) so `|K ∪ K*| = |K| + |K*| − 1`, and `|Ẑ| = |Z| − |K ∪ K*|`.
This is the cardinality the density bound `|𝒞_G(Ẑ)| = (1 − 1/k)(1 − 1/k*)|G| > ½|G|` rests on. -/
theorem zTilde_ncard_eq [Finite G] {M K Kstar : Subgroup G} (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (zTilde K Kstar).ncard = (Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) := by
  classical
  have hsub : ((K : Set G) ∪ (Kstar : Set G)) ⊆ ((K ⊔ Kstar : Subgroup G) : Set G) :=
    Set.union_subset (SetLike.coe_subset_coe.mpr le_sup_left)
      (SetLike.coe_subset_coe.mpr le_sup_right)
  have hZc : ((K ⊔ Kstar : Subgroup G) : Set G).ncard = Nat.card ↥K * Nat.card ↥Kstar := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Equiv.refl _)).symm.trans (card_kappaHall_sup_Kstar hKM hK hKstar)
  have hKc : (K : Set G).ncard = Nat.card ↥K := by
    rw [← Nat.card_coe_set_eq]; exact (Nat.card_congr (Equiv.refl _)).symm
  have hKstarc : (Kstar : Set G).ncard = Nat.card ↥Kstar := by
    rw [← Nat.card_coe_set_eq]; exact (Nat.card_congr (Equiv.refl _)).symm
  have hinter : (K : Set G) ∩ (Kstar : Set G) = {1} := by
    rw [← Subgroup.coe_inf, kappaHall_inf_Kstar_eq_bot hKM hK hKstar, Subgroup.coe_bot]
  have hunion : ((K : Set G) ∪ (Kstar : Set G)).ncard = Nat.card ↥K + Nat.card ↥Kstar - 1 := by
    have h := Set.ncard_union_add_ncard_inter (K : Set G) (Kstar : Set G)
    rw [hinter, Set.ncard_singleton, hKc, hKstarc] at h
    omega
  rw [zTilde, Set.ncard_sdiff hsub, hZc, hunion]
  exact nat_mul_sub_kl_identity Nat.card_pos Nat.card_pos

/-- Pure `ℕ` arithmetic for the `8/15 > 1/2` density step: for coprime odd `k, l > 1` one has
`k·l < 2(k−1)(l−1)`.  Equivalently `(k−2)(l−2) > 2`; the only odd pair `≥ 3` failing this is
`k = l = 3`, excluded by coprimality (`gcd 3 3 = 3 ≠ 1`).  Hence one factor is `≥ 5`. -/
private theorem card_kkstar_lt {k l : ℕ} (hk : Odd k) (hl : Odd l)
    (hk1 : k ≠ 1) (hl1 : l ≠ 1) (hcop : Nat.Coprime k l) :
    k * l < 2 * ((k - 1) * (l - 1)) := by
  obtain ⟨a, rfl⟩ := hk
  obtain ⟨b, rfl⟩ := hl
  have ha : 1 ≤ a := by omega
  have hb : 1 ≤ b := by omega
  have hnotboth : ¬ (a = 1 ∧ b = 1) := by
    rintro ⟨rfl, rfl⟩; exact absurd hcop (by decide)
  have hab : 2 ≤ a ∨ 2 ≤ b := by omega
  have key : 2 * a + 2 * b + 1 < 4 * (a * b) := by
    rcases hab with ha2 | hb2
    · have h1 : 2 * b ≤ a * b := Nat.mul_le_mul ha2 (le_refl b)
      have h2 : a ≤ a * b := by simpa using Nat.mul_le_mul (le_refl a) hb
      omega
    · have h1 : 2 * a ≤ a * b := by simpa [mul_comm] using Nat.mul_le_mul (le_refl a) hb2
      have h2 : b ≤ a * b := by simpa [mul_comm] using Nat.mul_le_mul (le_refl b) ha
      omega
  have e1 : 2 * a + 1 - 1 = 2 * a := by omega
  have e2 : 2 * b + 1 - 1 = 2 * b := by omega
  rw [e1, e2]
  nlinarith [key]

/-- **BG Theorem 14.7, the density bound `|𝒞_G(Ẑ)| > ½|G|`** (mmd L3975/L4051): the conjugacy
saturation of the TI-set `Ẑ` covers more than half of `G`.  This is the counting heart of the
`∃! M*` covering — a third nonconjugate type-`P` maximal subgroup would force a *second* `> ½|G|`
saturation piece disjoint from this one, which is impossible.

Proof chain: `Ẑ` is a TI-subset of `Z = K ⊔ K*` (`typeP_zTilde_isTI`) normalised by `Z`
(`typeP_family_Z_normalizes_T`, transported along `Ẑ = T`), so `|𝒞_G(Ẑ)| = |Ẑ|·[G : Z]`; with
`|Ẑ| = (k−1)(k*−1)` (`zTilde_ncard_eq`) and `|G| = |Z|·[G : Z] = k·k*·[G : Z]`
(`card_kappaHall_sup_Kstar`), the bound reduces to the pure inequality `k·k* < 2(k−1)(k*−1)`
(`card_kkstar_lt`) for the coprime (`coprime_card_kappaHall_Kstar`) odd `k = |K|`, `k* = |K*| > 1`
(`K* ≠ 1` is `typeP_structure`'s second conjunct). -/
theorem typeP_zTilde_conjClass_gt_half [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    Nat.card G < 2 * (conjClassSet (zTilde K Kstar)).ncard := by
  classical
  -- `Ẑ = T` (the family TI-set), via the `Z ⊓ N_σ` collapse.
  have hzeq : zTilde K Kstar = ((K ⊔ Kstar : Subgroup G) : Set G) \
      ⋃ N ∈ ZFamilyFinset M K,
        (((K ⊔ Kstar) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
    simp only [zTilde]
    rw [family_inf_msigma_union_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart]
  -- `Z` normalises `Ẑ` (transported from the family form).
  have hstab : ∀ l ∈ K ⊔ Kstar, MulAut.conj l • (zTilde K Kstar) = zTilde K Kstar := by
    intro l hl
    rw [hzeq]; exact typeP_family_Z_normalizes_T hG hM hP hKM hK hKstar hU l hl
  -- Saturation count `|𝒞_G(Ẑ)| = |Ẑ|·[G : Z]`.
  have hcount : (conjClassSet (zTilde K Kstar)).ncard
      = (zTilde K Kstar).ncard * (K ⊔ Kstar).index :=
    ncard_conjClassSet_of_isTISubset
      (typeP_zTilde_isTI hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart) hstab
  -- `|Ẑ| = (k − 1)(k* − 1)`.
  have hZc : (zTilde K Kstar).ncard = (Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) :=
    zTilde_ncard_eq hKM hK hKstar
  -- `|G| = |Z|·[G : Z] = k·k*·[G : Z]`.
  have hG_eq : Nat.card G = Nat.card ↥K * Nat.card ↥Kstar * (K ⊔ Kstar).index := by
    rw [← card_kappaHall_sup_Kstar hKM hK hKstar]
    exact (Subgroup.card_mul_index (K ⊔ Kstar)).symm
  have hidx_pos : 0 < (K ⊔ Kstar).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  -- `k, k*` are odd (divisors of `|G|`).
  have hKodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  have hKstarodd : Odd (Nat.card ↥Kstar) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Kstar)
  -- `k > 1`: a prime `p ∈ κ(M)` divides `|K|` (`card_kappaHall_ne_one`).
  have hKne1 : Nat.card ↥K ≠ 1 := card_kappaHall_ne_one hP hKM hK
  -- `k* > 1`: `K* ≠ ⊥` (Proposition 14.2's second conjunct).
  have hKstarne1 : Nat.card ↥Kstar ≠ 1 :=
    fun h => (typeP_structure hG hM hP hKM hK hKstar hU).2.1 (Subgroup.eq_bot_of_card_eq _ h)
  have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Kstar) :=
    coprime_card_kappaHall_Kstar hKM hK hKstar
  have harith : Nat.card ↥K * Nat.card ↥Kstar
      < 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1)) :=
    card_kkstar_lt hKodd hKstarodd hKne1 hKstarne1 hcop
  rw [hcount, hZc, hG_eq]
  calc Nat.card ↥K * Nat.card ↥Kstar * (K ⊔ Kstar).index
      < 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1)) * (K ⊔ Kstar).index :=
        mul_lt_mul_of_pos_right harith hidx_pos
    _ = 2 * ((Nat.card ↥K - 1) * (Nat.card ↥Kstar - 1) * (K ⊔ Kstar).index) :=
        mul_assoc _ _ _

open Classical in
/-- A reusable dummy `SigmaDecompositionData`: `length x = 1` iff `x ≠ 1` and `x` has a maximal
`σ`-subgroup.  The structure axiom `length_one_iff` pins this predicate across *all* carriers, and
the family/density machinery (`family_card_eq_two`, `exists_partner`, …) consumes `D` only through
`D.length x = 1`; so this dummy suffices — no genuine `σ`-decomposition theory is needed. -/
noncomputable def dummySigmaDecomposition (G : Type*) [Group G] : SigmaDecompositionData G where
  length := fun y => if y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty then 1 else 0
  length_one_iff := by
    intro y
    by_cases h : y ≠ 1 ∧ (maximalSigmaSubgroupsOfElement y).Nonempty <;> simp [h]

/-- Two subsets of a finite group, each covering more than half of it, must intersect. -/
theorem ncard_inter_nonempty_of_two_mul_gt [Finite G] {A B : Set G}
    (hA : Nat.card G < 2 * A.ncard) (hB : Nat.card G < 2 * B.ncard) :
    (A ∩ B).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hunion := Set.ncard_union_add_ncard_inter A B
  rw [hempty, Set.ncard_empty] at hunion
  have hle : (A ∪ B).ncard ≤ Nat.card G := by
    rw [← Set.ncard_univ G]
    exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  omega

/-- **BG Theorem 14.7, the density bound holds for every type-`P` maximal subgroup** (mmd L4053,
"we also have `|𝒞_G(S)| > ½|G|`"): for `H ∈ 𝓜_𝓟` there is a Hall `κ(H)`-subgroup `L` with
`L* = C_{Hσ}(L)` and `|𝒞_G(Ẑ_H)| > ½|G|`.  The same density count (`typeP_zTilde_conjClass_gt_half`)
run for `H`; the partner data for `H` is produced internally (`exists_partner`, fed the dummy
`σ`-decomposition).  Reused in the covering step of `typeP_duality`. -/
theorem exists_zTilde_conjClass_gt_half_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H : Subgroup G}
    (hHmax : H ∈ maximalSubgroups G) (hHP : IsTypeP H) :
    ∃ L Lstar Uu : Subgroup G, L ≤ H ∧ Ch03.IsHallSubgroup (kappa H) (L.subgroupOf H) ∧
      Lstar = OddOrder.BG.Ch3.S10.Msigma H ⊓ Subgroup.centralizer (L : Set G) ∧
      Ch03.IsHallSubgroup ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ) (Uu.subgroupOf H) ∧
      Nat.card G < 2 * (conjClassSet (zTilde L Lstar)).ncard := by
  classical
  haveI : IsSolvable ↥H := hG.solvable_of_mem_maximalSubgroups hHmax
  -- Hall `κ(H)`-subgroup `L` of `H`.
  obtain ⟨L', hL'⟩ := Ch03.hall_E_exists (G := ↥H) (kappa H)
  have hLeq : (L'.map H.subtype).subgroupOf H = L' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L'
  have hL : Ch03.IsHallSubgroup (kappa H) ((L'.map H.subtype).subgroupOf H) := by
    rw [hLeq]; exact hL'
  have hLH : L'.map H.subtype ≤ H := Subgroup.map_subtype_le L'
  set L := L'.map H.subtype with hLdef
  set Lstar := OddOrder.BG.Ch3.S10.Msigma H ⊓ Subgroup.centralizer (L : Set G) with hLstar
  -- Hall `(κ(H) ∪ σ(H))'`-subgroup `U` of `H`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥H) ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ)
  have hUeq : (U'.map H.subtype).subgroupOf H = U' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa H ∪ OddOrder.BG.Ch3.S10.sigma H)ᶜ)
      ((U'.map H.subtype).subgroupOf H) := by rw [hUeq]; exact hU'
  -- Partner data for `H`, then the density bound.
  obtain ⟨Hstar, hHstarne, hHstarmem, hpart⟩ :=
    exists_partner hG (dummySigmaDecomposition G) hHmax hHP hLH hL hLstar hU
  exact ⟨L, Lstar, U'.map H.subtype, hLH, hL, hLstar, hU,
    typeP_zTilde_conjClass_gt_half hG hHmax hHP hLH hL hLstar hU hHstarmem hHstarne hpart⟩

/-- Dual of `isPiElementCompl_mem_left_of_commute`: a `π`-element of `Z = A ⊔ B` (with `A` a
`πᶜ`-group, `B` a `π`-group commuting with `A`) lies in `B`.  (Swap the roles of `A`, `B` and
`π`, `πᶜ`.) -/
theorem isPiElement_mem_right_of_commute [Finite G] {A B Z : Subgroup G} {π : Set ℕ}
    (hswap : Z = A ⊔ B) (hcent : B ≤ Subgroup.centralizer (A : Set G))
    (hAπc : Subgroup.IsPiSubgroup πᶜ A) (hBπ : Subgroup.IsPiSubgroup π B)
    {b : G} (hbZ : b ∈ Z) (hbπ : IsPiElement π b) : b ∈ B := by
  have hAcent : A ≤ Subgroup.centralizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    exact fun c hc => (Subgroup.mem_centralizer_iff.mp (hcent hc) a ha).symm
  exact isPiElementCompl_mem_left_of_commute (A := B) (B := A) (π := πᶜ)
    (by rw [hswap, sup_comm]) hAcent (by rwa [compl_compl]) hAπc hbZ (by rwa [compl_compl])

/-- **BG Theorem 14.7 covering, the `σ`-part matching** (mmd L4053): if `t` lies in both
`Ẑ_M = (K ⊔ K*) − (K ∪ K*)` (with `K` a `σ(M)′`-group, `K*` a `σ(M)`-group commuting with `K`) and
in `L ⊔ L*` but not in `L` (with `L` a `σ(H)′`-group, `L*` a `σ(H)`-group commuting with `L`), then
`L*` meets one of `K`, `K*` nontrivially.  Proof: the `σ(H)`-part `w` of `t` is a nontrivial
element of `L*` (else `t = (σ(H)′-part) ∈ L`), and `w ∈ ⟨t⟩ ⊆ K ⊔ K*`; its `σ(M)`- and
`σ(M)′`-parts are powers of `w` (so in `L*`) lying in `K*` resp. `K`, and at least one is
nontrivial.  This realizes BG's "`T ∩ S ≠ ∅ ⟹ L* ∩ Kᵢ* ≠ 1`". -/
theorem exists_inf_ne_bot_of_mem_zTilde_inter [Finite G] {K Kstar L Lstar : Subgroup G}
    {πM πH : Set ℕ}
    (hKπ : Subgroup.IsPiSubgroup πMᶜ K) (hKstarπ : Subgroup.IsPiSubgroup πM Kstar)
    (hKcent : Kstar ≤ Subgroup.centralizer (K : Set G))
    (hLπ : Subgroup.IsPiSubgroup πHᶜ L) (hLstarπ : Subgroup.IsPiSubgroup πH Lstar)
    (hLcent : Lstar ≤ Subgroup.centralizer (L : Set G))
    {t : G} (htZ : t ∈ K ⊔ Kstar) (htnL : t ∉ L) (htZ' : t ∈ L ⊔ Lstar) :
    Lstar ⊓ K ≠ ⊥ ∨ Lstar ⊓ Kstar ≠ ⊥ := by
  classical
  -- `σ(H)`-decompose `t = w * v`; `v ∈ L`, `w ∈ L*`, and `w ≠ 1`.
  obtain ⟨w, v, hwv, -, hwπ, hvπ, hwz, hvz⟩ := exists_isPiElement_mul πH t
  have hvL : v ∈ L := isPiElementCompl_mem_left_of_commute rfl hLcent hLπ hLstarπ
    ((Subgroup.zpowers_le.mpr htZ') hvz) hvπ
  have hwLstar : w ∈ Lstar := isPiElement_mem_right_of_commute rfl hLcent hLπ hLstarπ
    ((Subgroup.zpowers_le.mpr htZ') hwz) hwπ
  have hw1 : w ≠ 1 := fun hw => htnL (by rw [show t = v by rw [← hwv, hw, one_mul]]; exact hvL)
  -- `σ(M)`-decompose `w = a * b`; `a ∈ K*`, `b ∈ K`, both powers of `w` (so in `L*`).
  have hwZ : w ∈ K ⊔ Kstar := (Subgroup.zpowers_le.mpr htZ) hwz
  obtain ⟨a, b, hab, -, haπ, hbπ, haz, hbz⟩ := exists_isPiElement_mul πM w
  have haKstar : a ∈ Kstar := isPiElement_mem_right_of_commute rfl hKcent hKπ hKstarπ
    ((Subgroup.zpowers_le.mpr hwZ) haz) haπ
  have hbK : b ∈ K := isPiElementCompl_mem_left_of_commute rfl hKcent hKπ hKstarπ
    ((Subgroup.zpowers_le.mpr hwZ) hbz) hbπ
  have haLstar : a ∈ Lstar := (Subgroup.zpowers_le.mpr hwLstar) haz
  have hbLstar : b ∈ Lstar := (Subgroup.zpowers_le.mpr hwLstar) hbz
  -- `w = a * b ≠ 1`, so one factor is nontrivial.
  have hor : a ≠ 1 ∨ b ≠ 1 := by
    by_contra h; push Not at h
    exact hw1 (by rw [← hab, h.1, h.2, mul_one])
  rcases hor with ha1 | hb1
  · exact Or.inr fun hbot => ha1 (by
      have : a ∈ Lstar ⊓ Kstar := Subgroup.mem_inf.mpr ⟨haLstar, haKstar⟩
      rwa [hbot, Subgroup.mem_bot] at this)
  · exact Or.inl fun hbot => hb1 (by
      have : b ∈ Lstar ⊓ K := Subgroup.mem_inf.mpr ⟨hbLstar, hbK⟩
      rwa [hbot, Subgroup.mem_bot] at this)

/-- **BG Proposition 14.2(f)** (mmd L3838): every `σ(M)`-subgroup `Y < ⊤` of `G` meeting `K*`
nontrivially lies in `M_σ`.  Not among `typeP_structure`'s packaged conjuncts; derived here from
Corollary 12.16 (`Y` is `G`-conjugate into `M_σ`) and Proposition 14.2(d) (the conjugator lies in
`M`, since it fixes a nontrivial element of `K*`).  A step of the partner-symmetry argument of
Theorem 14.7. -/
theorem typeP_sigma_subgroup_le_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {Y : Subgroup G} (hYlt : Y < ⊤)
    (hYpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Y)
    (hYmeet : Y ⊓ Kstar ≠ ⊥) :
    Y ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have hYne : Y ≠ ⊥ := fun h => hYmeet (by rw [h, bot_inf_eq])
  -- Corollary 12.16: `Y` is `G`-conjugate into `M_σ`.
  obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hM hYne hYlt hYpi
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM hN hnc)
  -- A nontrivial common element `y ∈ Y ⊓ K*`.
  obtain ⟨ysub, hysub1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYmeet
  have hy1 : (ysub : G) ≠ 1 := fun h => hysub1 (OneMemClass.coe_eq_one.mp h)
  have hyY : (ysub : G) ∈ Y := (Subgroup.mem_inf.mp ysub.2).1
  have hyKstar : (ysub : G) ∈ Kstar := (Subgroup.mem_inf.mp ysub.2).2
  -- `conj g • y ∈ M_σ ⊆ M`, so `y ∈ conj g⁻¹ • M`.
  have hyMconj : (ysub : G) ∈ MulAut.conj g⁻¹ • M := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show (MulAut.conj g⁻¹)⁻¹ • (ysub : G) = MulAut.conj g • (ysub : G) by
        rw [← map_inv MulAut.conj g⁻¹, inv_inv]]
    exact OddOrder.BG.Ch3.S10.Msigma_le M
      (hg (Subgroup.smul_mem_pointwise_smul (ysub : G) (MulAut.conj g) Y hyY))
  -- Proposition 14.2(d): `K* ⊓ Mᵍ⁻¹ ≠ 1` forces `g⁻¹ ∈ M`.
  have hginvM : g⁻¹ ∈ M := by
    by_contra hg'
    exact hy1 (Subgroup.mem_bot.mp
      (((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.1 g⁻¹ hg') ▸
        Subgroup.mem_inf.mpr ⟨hyKstar, hyMconj⟩))
  have hgM : g ∈ M := inv_inv g ▸ M.inv_mem hginvM
  -- `conj g` fixes `M` and `M_σ`; descend `conj g • Y ≤ M_σ` to `Y ≤ M_σ`.
  have hconjM : MulAut.conj g • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)
  have hgMsigma :
      MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [← Msigma_conj_smul, hconjM]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp (hgMsigma ▸ hg)

/-- **BG Theorem 14.7(2)(3), partner symmetry** (mmd L4061): the partner `M*` carries the dual
Hall structure — `K*` is a Hall `κ(M*)`-subgroup of `M*` and `K = C_{M*_σ}(K*)`.  So the roles of
`(M, K, K*)` and `(M*, K*, K)` are symmetric.

This is short here (not BG's end-of-proof `Hall σ(M)`-subgroup argument) because the family
machinery already produced `M*`'s Hall `κ(M*)`-subgroup `KN` with `Z = KN ⊔ C_{M*_σ}(KN)`
(`typeP_family_member_data`) and `Z ⊓ M*_σ = K` (`partner_canonical_eq`); two applications of
`isPiSubgroup_le_left_of_commute` (with `π = σ(M*)`: `K` is the `σ(M*)`-part of `Z`, while `KN` and
`K*` are both the `σ(M*)′`-part) give `KN = K*`. -/
theorem typeP_partner_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ Kstar ≤ Mstar ∧
      Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
      K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G) := by
  classical
  obtain ⟨hMstarmax, hMstarP, hZMstar, KN, hKNMstar, hKN_hall, hsw, hcanon, -⟩ :=
    typeP_family_member_data hG hM hP hKM hK hKstar hU hMstarmem
  -- The partner's canonical factor `C_{M*_σ}(KN) = K`.
  have hcanonK : OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (KN : Set G) = K := by
    rw [hcanon]; exact partner_canonical_eq hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  have hnc : ¬ IsConjugateSubgroup M Mstar :=
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne)
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma Mstar) :=
    sigma_disjoint_of_nonconjugate hG hM hMstarmax hnc
  -- `π`-subgroup data for `π = σ(M*)`: `K` is `σ(M*)`, `K*`/`KN` are `σ(M*)′`.
  have hK_piMstar : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar) K := fun q hq =>
    kappaHall_primes_subset_sigma_partner hG hM hP hKM hK hKstar hU hpart
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  have hKstar_piMstarc :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ Kstar := fun q hq =>
    Set.disjoint_left.mp hσdisj (Kstar_isPiSubgroup_sigma hKstar q hq)
  have hKN_piMstarc :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ KN := fun q hq =>
    kappa_subset_sigmaCompl (hKN_hall.1 q
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNMstar).toEquiv]; exact hq))
  -- `K` centralizes both `K*` and `KN`.
  have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hKstar ▸ hs)).2 k hk).symm
  have hKcKN : K ≤ Subgroup.centralizer (KN : Set G) := hcanonK ▸ inf_le_right
  -- `KN = K*`: each lies in the other's `σ(M*)′`-part of `Z`.
  have hKNle : KN ≤ Kstar := isPiSubgroup_le_left_of_commute (π := OddOrder.BG.Ch3.S10.sigma Mstar)
    (by rw [sup_comm]) hKcKstar hKstar_piMstarc hK_piMstar (by rw [hsw]; exact le_sup_left)
    hKN_piMstarc
  have hKstarle : Kstar ≤ KN := isPiSubgroup_le_left_of_commute
    (π := OddOrder.BG.Ch3.S10.sigma Mstar) (hsw.trans (by rw [hcanonK])) hKcKN hKN_piMstarc
    hK_piMstar le_sup_right hKstar_piMstarc
  have hKNeq : KN = Kstar := le_antisymm hKNle hKstarle
  exact ⟨hMstarmax, hMstarP, le_sup_right.trans hZMstar, hKNeq ▸ hKN_hall,
    (hKNeq ▸ hcanonK).symm⟩

/-- **BG Theorem 14.7(1)** (mmd L3964): `ℳ(C_G(Y)) = {M*}` for every `Y ∈ ℰ¹(K)`.  This is
Proposition 14.2(c) applied to the *partner* `M*`: by the partner symmetry
(`typeP_partner_structure`) `K*` is a Hall `κ(M*)`-subgroup of `M*` and `K = C_{M*_σ}(K*)`, i.e.
`K` plays the `K*`-role for `M*`, so `14.2(c)` for `M*` yields the unique-maximal conclusion for
lines of `K`.  The `K`-side companion of Proposition 14.2(c); the covering step of Theorem 14.7
uses it to conjugate a type-`P` subgroup to `M*`. -/
theorem typeP_partner_centralizer_singleton [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {p : ℕ} [Fact p.Prime] {Y : Subgroup G} (hY : Y ∈ elemAbelianOfRank G p 1) (hYK : Y ≤ K) :
    maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar} := by
  classical
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hK_eq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hU_Mstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  exact (typeP_structure hG hMstarmax hMstarP hKstarMstar hKstar_hall hK_eq hU_Mstar).2.2.2.2.2.1
    p Fact.out Y hY hYK

/-- **BG Theorem 14.7(7), the covering** (mmd L4053): every type-`P` maximal subgroup `H` is
conjugate to `M` or to its partner `M*`.

Proof: both `Ẑ_M` and `Ẑ_H` have conjugacy saturation `> ½|G|`
(`typeP_zTilde_conjClass_gt_half`, `exists_zTilde_conjClass_gt_half_of_isTypeP`), so the
saturations meet (`ncard_inter_nonempty_of_two_mul_gt`); a common element gives `t ∈ Ẑ_M`,
`s ∈ Ẑ_H` with `t = c • s`.  The `σ`-part matching (`exists_inf_ne_bot_of_mem_zTilde_inter`) then
yields a nontrivial `L*ᶜ ⊓ K` or `L*ᶜ ⊓ K*` (here `L*ᶜ = c • L*`); a line `Y` in it satisfies
`ℳ(C_G(Y)) = {M}` (Proposition 14.2(c), `K*`-case) or `{M*}` (`typeP_partner_centralizer_singleton`,
`K`-case), while `c⁻¹ • Y ∈ ℰ¹(L*)` gives `ℳ(C_G(c⁻¹•Y)) = {H}` (Proposition 14.2(c) for `H`).
Transporting by `c` shows `c • H` is a maximal subgroup over `C_G(Y)`, so `c • H = M` or `M*`. -/
theorem typeP_covering [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {H : Subgroup G} (hHmax : H ∈ maximalSubgroups G) (hHP : IsTypeP H) :
    IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar := by
  classical
  have hMbound := typeP_zTilde_conjClass_gt_half hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  obtain ⟨L, Lstar, Uu, hLH, hL_hall, hLstar_eq, hU_H, hHbound⟩ :=
    exists_zTilde_conjClass_gt_half_of_isTypeP hG hHmax hHP
  obtain ⟨u, huM, huH⟩ := ncard_inter_nonempty_of_two_mul_gt hMbound hHbound
  obtain ⟨t, htM, a, hat⟩ := huM
  obtain ⟨s, hsH, b, hbs⟩ := huH
  simp only [zTilde, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or] at htM hsH
  obtain ⟨htZ, htK, htKstar⟩ := htM
  obtain ⟨hsZ, hsL, hsLstar⟩ := hsH
  set c := a⁻¹ * b with hc_def
  -- `t = c • s`.
  have htcs : MulAut.conj c • s = t := by
    have key : b * s * b⁻¹ = a * t * a⁻¹ := hbs.trans hat.symm
    rw [MulAut.smul_def, MulAut.conj_apply, hc_def, mul_inv_rev, inv_inv]
    calc a⁻¹ * b * s * (b⁻¹ * a)
        = a⁻¹ * (b * s * b⁻¹) * a := by group
      _ = a⁻¹ * (a * t * a⁻¹) * a := by rw [key]
      _ = t := by group
  have hcancel1 : ∀ X : Subgroup G, MulAut.conj c⁻¹ • (MulAut.conj c • X) = X := fun X => by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hcancel2 : ∀ X : Subgroup G, MulAut.conj c • (MulAut.conj c⁻¹ • X) = X := fun X => by
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  -- Matching inputs.
  have hcardL : Nat.card ↥(MulAut.conj c • L) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hcardLstar : Nat.card ↥(MulAut.conj c • Lstar) = Nat.card ↥Lstar :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hKπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ K :=
    kappaHall_isPiSubgroup_sigmaCompl hKM hK
  have hKstarπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar :=
    Kstar_isPiSubgroup_sigma hKstar
  have hKcent : Kstar ≤ Subgroup.centralizer (K : Set G) := hKstar ▸ inf_le_right
  have hcLπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ (MulAut.conj c • L) := by
    intro q hq
    rw [hcardL] at hq
    exact kappa_subset_sigmaCompl
      (hL_hall.1 q (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH).toEquiv]))
  have hcLstarπ :
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H) (MulAut.conj c • Lstar) := by
    intro q hq
    rw [hcardLstar] at hq
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup H q (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hq).1, (Nat.dvd_of_mem_primeFactors hq).trans
        (Subgroup.card_dvd_of_le (hLstar_eq ▸ inf_le_left)), Nat.card_pos.ne'⟩)
  have hcLcent : MulAut.conj c • Lstar ≤ Subgroup.centralizer ((MulAut.conj c • L : Subgroup G)) := by
    rw [← centralizer_conj_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hLstar_eq ▸ inf_le_right)
  have htnL : t ∉ MulAut.conj c • L := fun ht =>
    hsL (Subgroup.smul_mem_pointwise_smul_iff.mp (htcs.symm ▸ ht))
  have htZ' : t ∈ (MulAut.conj c • L) ⊔ (MulAut.conj c • Lstar) := by
    rw [← htcs, ← Subgroup.smul_sup]
    exact Subgroup.smul_mem_pointwise_smul s (MulAut.conj c) (L ⊔ Lstar) hsZ
  have hmatch := exists_inf_ne_bot_of_mem_zTilde_inter (πM := OddOrder.BG.Ch3.S10.sigma M)
    (πH := OddOrder.BG.Ch3.S10.sigma H) hKπ hKstarπ hKcent hcLπ hcLstarπ hcLcent htZ htnL htZ'
  -- Common tail: a line `Y ≤ c • L*` with `ℳ(C_G(Y)) = {N}` gives `H ~ N`.
  have hfinish : ∀ {N : Subgroup G} {p : ℕ}, p.Prime → ∀ {Y : Subgroup G},
      Y ∈ elemAbelianOfRank G p 1 → Y ≤ MulAut.conj c • Lstar →
      maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {N} →
      IsConjugateSubgroup H N := by
    intro N p hp Y hYea hYcL hN_sing
    have hcY : MulAut.conj c⁻¹ • Y ≤ Lstar := by
      have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff
        (a := MulAut.conj c⁻¹) |>.mpr hYcL
      rwa [hcancel1 Lstar] at h1
    have hcYea : MulAut.conj c⁻¹ • Y ∈ elemAbelianOfRank G p 1 :=
      conj_smul_mem_elemAbelianOfRank c⁻¹ hYea
    have hH_sing := (typeP_structure hG hHmax hHP hLH hL_hall hLstar_eq hU_H).2.2.2.2.2.1
      p hp _ hcYea hcY
    have hCle : Subgroup.centralizer ((MulAut.conj c⁻¹ • Y : Subgroup G) : Set G) ≤ H :=
      (mem_maximalSubgroupsContaining.mp (hH_sing.symm ▸ Set.mem_singleton H)).2
    have hCYle : Subgroup.centralizer (Y : Set G) ≤ MulAut.conj c • H := by
      have h1 := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj c) |>.mpr hCle
      rwa [centralizer_conj_smul, hcancel2 Y] at h1
    have hcHN : MulAut.conj c • H = N := by
      have hmem : MulAut.conj c • H ∈ maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) :=
        mem_maximalSubgroupsContaining.mpr ⟨isCoatom_conj_smul (mem_maximalSubgroups.mp hHmax), hCYle⟩
      rw [hN_sing] at hmem; exact Set.eq_of_mem_singleton hmem
    exact ⟨c, hcHN⟩
  -- Extract a line `Y` from the nontrivial intersection and finish.
  rcases hmatch with hne | hne
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hne (Subgroup.eq_bot_of_card_eq _ h))
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyord' : orderOf (y : G) = p :=
      (orderOf_injective _ (MulAut.conj c • Lstar ⊓ K).subtype_injective y).trans hyord
    have hYcard : Nat.card ↥(Subgroup.zpowers (y : G)) = p := by rw [Nat.card_zpowers, hyord']
    have hYea : Subgroup.zpowers (y : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    have hYS : Subgroup.zpowers (y : G) ≤ MulAut.conj c • Lstar ⊓ K :=
      Subgroup.zpowers_le.mpr y.2
    exact Or.inr (hfinish hp hYea (hYS.trans inf_le_left)
      (typeP_partner_centralizer_singleton hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
        hYea (hYS.trans inf_le_right)))
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
      (fun h => hne (Subgroup.eq_bot_of_card_eq _ h))
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hyord' : orderOf (y : G) = p :=
      (orderOf_injective _ (MulAut.conj c • Lstar ⊓ Kstar).subtype_injective y).trans hyord
    have hYcard : Nat.card ↥(Subgroup.zpowers (y : G)) = p := by rw [Nat.card_zpowers, hyord']
    have hYea : Subgroup.zpowers (y : G) ∈ elemAbelianOfRank G p 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
    have hYS : Subgroup.zpowers (y : G) ≤ MulAut.conj c • Lstar ⊓ Kstar :=
      Subgroup.zpowers_le.mpr y.2
    exact Or.inl (hfinish hp hYea (hYS.trans inf_le_left)
      ((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.2.1 p hp _ hYea (hYS.trans inf_le_right)))

/-- A Hall `κ(N)`-subgroup `K'` of a maximal `N`, lying inside a nilpotent subgroup `W`, is cyclic.
Since `κ(N) ⊆ τ₁(N) ∪ τ₃(N)`, every prime `p ∣ |K'|` has `pRank N p = 1`, so `pRank K' p ≤ 1`
(`= 0` off `π(K')`); and `K' ≤ W` nilpotent makes `K'` nilpotent.  An odd nilpotent group with
`pRank ≤ 1` everywhere is cyclic (`isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one`).  Used to
make both Hall factors of `Z` cyclic in `typeP_Z_isCyclic`. -/
theorem isCyclic_kappaHall_of_le_nilpotent [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {N K' W : Subgroup G} (hK'N : K' ≤ N)
    (hK'_hall : Ch03.IsHallSubgroup (kappa N) (K'.subgroupOf N))
    (hK'W : K' ≤ W) [Group.IsNilpotent ↥W] : IsCyclic ↥K' := by
  haveI : Group.IsNilpotent ↥K' :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK'W)
  have hodd : Odd (Nat.card ↥K') :=
    hG.odd.of_dvd_nat ((Subgroup.card_dvd_of_le hK'N).trans (Subgroup.card_subgroup_dvd_card N))
  refine isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one hodd fun p hp => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hpK : p ∈ (Nat.card ↥K').primeFactors
  · have hpκ : p ∈ kappa N := hK'_hall.1 p (by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'N).toEquiv])
    have hpτ : pRank ↥N p = 1 := hpκ.2.1.elim tau1_pRank_eq_one tau3_pRank_eq_one
    exact le_trans (pRank_le_of_injective (Subgroup.inclusion_injective hK'N)) (le_of_eq hpτ)
  · by_contra hcon
    exact hpK (OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank (by omega))

/-- For a type-`P₂` maximal subgroup `M`, the `σ`-core `M_σ` is nilpotent.  Since `κ(M)` always
satisfies `κ(M) ⊆ π(M) ∖ σ(M)` and `IsTypeP2` makes this inclusion *proper*, there is a prime
`p ∈ π(M) ∖ (σ(M) ∪ κ(M))`; a maximal-rank elementary abelian `p`-subgroup `A ≤ M` then meets the
hypotheses of Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`: `p ∈ π(M)`, `p ∉ σ(M)`,
`p ∉ κ(M)`, `A ∈ ℰ_p^{r_p(M)}`), whose third conclusion is `IsNilpotent M_σ`.  This drives the
cyclicity of `Z = K ⊔ K*` in `typeP_Z_isCyclic` (BG 14.7(d)). -/
theorem msigma_isNilpotent_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) :
    Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  classical
  -- `κ(M) ⊆ π(M) ∖ σ(M)`: every prime in `κ(M)` divides `|M|` (a rank-one witness `P ≤ M` has
  -- order `p`) and avoids `σ(M)` (`κ ⊆ σ′`).  `IsTypeP2` makes the inclusion proper.
  have hsub : kappa M ⊆ sigmaComplementPrimes M := by
    intro p hp
    obtain ⟨hp_prime, _, P, hPelem, hPM, _⟩ := id hp
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp_prime, ?_, Nat.card_pos.ne'⟩, kappa_subset_sigmaCompl hp⟩
    rw [← hPcard]; exact Subgroup.card_dvd_of_le hPM
  obtain ⟨p, hpπ, hpκ⟩ := Set.exists_of_ssubset (ssubset_of_subset_of_ne hsub hP2.2)
  obtain ⟨hpM, hpσ⟩ := hpπ
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpM
  haveI : Fact p.Prime := ⟨hp⟩
  -- A maximal-rank elementary abelian `p`-subgroup `A = B.map M.subtype ≤ M`.
  obtain ⟨B, hBea, hBlog⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p)
      (n := pRank ↥M p) (one_le_pRank_of_mem_primeFactors hpM) (le_refl _)
  obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
  have hjeq : j = pRank ↥M p := by
    have hsq := le_antisymm (le_pRank B hBea) hBlog
    rwa [hj, Nat.log_pow hp.one_lt] at hsq
  have hAmem : B.map M.subtype ∈ elemAbelianOfRank G p (pRank ↥M p) := by
    refine ⟨Subgroup.IsElementaryAbelian.map M.subtype_injective hBea, ?_⟩
    rw [Subgroup.card_map_of_injective M.subtype_injective, hj, hjeq]
  exact (msigma_structure_of_notMem_sigma_kappa hG hM hpM hpσ hpκ hAmem
    (Subgroup.map_subtype_le _)).2.2

/-- **BG Theorem 14.7, cyclicity of `Z = K ⊔ K*`** (mmd L4041, conjunct (d)): for a type-`P`
maximal `M` with its nonconjugate partner `M*` (the unique other member of the `Z`-family), the
group `Z = K ⊔ K*` is cyclic.  By `isTypeP2_or_isTypeP2_partner` one of `M`, `M*` is type-`P₂`;
in either case the Hall `κ`-factor of the `P₂` member has prime order (cyclic, `typeP_structure`
clause (g)), while the other factor is a Hall `κ`-subgroup of the partner lying inside the
*nilpotent* `σ`-core of the `P₂` member (`msigma_isNilpotent_of_isTypeP2` +
`isCyclic_kappaHall_of_le_nilpotent`, whose Hall-witness `N` and nilpotent ambient `W` differ).
Two coprime cyclic factors give `Z` cyclic (`isCyclic_kappaHall_sup_Kstar_of_cyclic`). -/
theorem typeP_Z_isCyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar) :
    IsCyclic ↥(K ⊔ Kstar) := by
  classical
  -- Partner symmetry: `K*` is Hall `κ(M*)` of `M*`, and `K = C_{M*_σ}(K*)`.
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  rcases isTypeP2_or_isTypeP2_partner hG D hM hP hKM hK hKstar hU hpart with hM2 | hMstar2
  · -- `M` is type-`P₂`: `|K|` prime ⟹ `K` cyclic; `K* ≤ M_σ` (nilpotent) ⟹ `K*` cyclic.
    obtain ⟨q, hq, hKq, -⟩ := ((typeP_structure hG hM hP hKM hK hKstar hU).2.2.2.2.1 hM2).2
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : IsCyclic ↥K := isCyclic_of_prime_card hKq
    haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      msigma_isNilpotent_of_isTypeP2 hG hM hM2
    haveI : IsCyclic ↥Kstar :=
      isCyclic_kappaHall_of_le_nilpotent hG hKstarMstar hKstar_hall (hKstar.le.trans inf_le_left)
    exact isCyclic_kappaHall_sup_Kstar_of_cyclic hKM hK hKstar
  · -- `M*` is type-`P₂`: `|K*|` prime ⟹ `K*` cyclic; `K ≤ M*_σ` (nilpotent) ⟹ `K` cyclic.
    haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
      ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
    have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
      Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
    have hUstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
        ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
    obtain ⟨q, hq, hKstarq, -⟩ :=
      ((typeP_structure hG hMstarmax hMstarP hKstarMstar hKstar_hall hKeq hUstar).2.2.2.2.1
        hMstar2).2
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : IsCyclic ↥Kstar := isCyclic_of_prime_card hKstarq
    haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) :=
      msigma_isNilpotent_of_isTypeP2 hG hMstarmax hMstar2
    haveI : IsCyclic ↥K :=
      isCyclic_kappaHall_of_le_nilpotent hG hKM hK (hKeq.le.trans inf_le_left)
    have hcyc : IsCyclic ↥(Kstar ⊔ K) :=
      isCyclic_kappaHall_sup_Kstar_of_cyclic hKstarMstar hKstar_hall hKeq
    rw [sup_comm]; exact hcyc

/-- **BG Theorem 14.7, the unique nonconjugate partner `M*`** (mmd L3962-3971, parts (1)-(7) +
appendix item (4)): for a type-`P` maximal `M`, there is a *unique* maximal subgroup `M*` that is
type-`P`, nonconjugate to `M`, has `K*` as a Hall `κ(M*)`-subgroup with `K = C_{M*_σ}(K*)`, makes
`Z = K ⊔ K*` cyclic with `Ẑ` a TI-set, has one of `M`, `M*` type-`P₂`, and covers every type-`P`
maximal up to conjugacy.

Existence is the canonical partner of `exists_partner`, its data assembled from
`typeP_partner_structure` (maximal/type-P/`K* ≤ M*`/Hall `κ(M*)`/`K = C_{M*_σ}(K*)`),
`typeP_family_pairwise_nonconjugate`, `typeP_Z_isCyclic`, `typeP_zTilde_isTI`,
`isTypeP2_or_isTypeP2_partner`, and `typeP_covering`.

**Uniqueness** turns on the partner-symmetry conjunct `K = C_{M*_σ}(K*)` (BG 14.7(3), appendix (4)):
it makes `K` the `K*`-role subgroup of any competitor `M*'`, so Proposition 14.2(c) for `M*'`
(`typeP_structure`, last conjunct) gives `ℳ(C_G(X)) = {M*'}` for a line `X ∈ ℰ¹(K)`, which also
equals `{M*}` (Theorem 14.7(1), `typeP_partner_centralizer_singleton`), forcing `M*' = M*`.

The partner-symmetry conjunct is *essential*: without it the `∃!` is false, since
`M*' := (M*)ᵈ` for `d ∈ N_{M_σ}(K*) ∖ K*` (which exists when `M_σ` is nilpotent and `K* ⊊ M_σ`,
e.g. `M` type-`P₂`) is nonconjugate to `M*`, still has `K*` Hall `κ(M*')` (as `d` normalizes `K*`),
and satisfies every other conjunct, yet `M*' ≠ M*`. -/
theorem typeP_partner_existsUnique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
        K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  classical
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hM hP hKM hK hKstar hU
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  -- A line `X = ⟨x⟩ ∈ ℰ¹(K)` (needed for both the existence data and the uniqueness pin).
  obtain ⟨p, hpκ⟩ := id hP
  have hp : p.Prime := prime_of_mem_kappa hpκ
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card ↥K := by
    obtain ⟨_, _, P, hPelem, hPM, _⟩ := id hpκ
    have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
    have hpdvdM : p ∣ Nat.card ↥M := by rw [← hPcard]; exact Subgroup.card_dvd_of_le hPM
    have hsplit : p ∣ Nat.card ↥(K.subgroupOf M) * (K.subgroupOf M).index := by
      rw [Subgroup.card_mul_index]; exact hpdvdM
    have hpKsub : p ∣ Nat.card ↥(K.subgroupOf M) := by
      rcases hp.dvd_mul.mp hsplit with h | h
      · exact h
      · exact absurd hpκ (hK.2 p (Nat.mem_primeFactors.mpr
          ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hpKsub
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxord : orderOf (x : G) = p := (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = p := by rw [Nat.card_zpowers, hxord]
  have hXelem : Subgroup.zpowers (x : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXK : Subgroup.zpowers (x : G) ≤ K := Subgroup.zpowers_le.mpr x.2
  -- `ℳ(C_G(X)) = {M*}` (Theorem 14.7(1)).
  have h0 : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G))
      = {Mstar} :=
    typeP_partner_centralizer_singleton hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hXelem hXK
  refine ⟨Mstar, ⟨hMstarmax, hMstarP,
    typeP_family_pairwise_nonconjugate hG hM hP hKM hK hKstar hU (Or.inl rfl) hMstarmem
      (Ne.symm hMstarne),
    ⟨hKstarMstar, hKstar_hall, hKeq⟩,
    typeP_Z_isCyclic hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart,
    typeP_zTilde_isTI hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart,
    isTypeP2_or_isTypeP2_partner hG D hM hP hKM hK hKstar hU hpart,
    fun H hHmax hHP =>
      typeP_covering hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hHmax hHP⟩, ?_⟩
  -- Uniqueness: any competitor `M*'` satisfies `ℳ(C_G(X)) = {M*'}` via the partner symmetry.
  rintro Mstar' ⟨hMstar'max, hMstar'P, -, ⟨hKstarMstar', hKstar'_hall, hKeq'⟩, -, -, -, -⟩
  haveI : IsSolvable ↥Mstar' := hG.solvable_of_mem_maximalSubgroups hMstar'max
  obtain ⟨U'', hU''⟩ := Ch03.hall_E_exists (G := ↥Mstar')
    ((kappa Mstar' ∪ OddOrder.BG.Ch3.S10.sigma Mstar')ᶜ)
  have hU''eq : (U''.map Mstar'.subtype).subgroupOf Mstar' = U'' :=
    Subgroup.comap_map_eq_self_of_injective Mstar'.subtype_injective U''
  have hUstar' : Ch03.IsHallSubgroup ((kappa Mstar' ∪ OddOrder.BG.Ch3.S10.sigma Mstar')ᶜ)
      ((U''.map Mstar'.subtype).subgroupOf Mstar') := by rw [hU''eq]; exact hU''
  have h' : maximalSubgroupsContaining (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G))
      = {Mstar'} :=
    (typeP_structure hG hMstar'max hMstar'P hKstarMstar' hKstar'_hall hKeq' hUstar').2.2.2.2.2.1
      p hp _ hXelem hXK
  have hmem : Mstar' ∈ maximalSubgroupsContaining
      (Subgroup.centralizer ((Subgroup.zpowers (x : G)) : Set G)) := by
    rw [h']; exact Set.mem_singleton _
  rw [h0, Set.mem_singleton_iff] at hmem
  exact hmem

/-- **Derived subgroup via a `σ`-complement** (BG 14.7(h), Proposition 14.2(a) skeleton, mmd L4061):
for any §12 `E`-setup of `M` (so `M = M_σ ⋊ E`), the derived subgroup `M' = [M,M]` equals
`M_σ ⊔ E'` where `E' = [E,E]` is the derived subgroup of the `σ(M)'`-complement.

`⊇` is `Msigma_le_derived` (`M_σ ≤ M'`) plus `commutator_mono` (`E' ≤ M'`).  For `⊆`, an element
`x ∈ M'` decomposes as `x = a·b` (`a ∈ M_σ`, `b ∈ E`) inside `↥M = M_σ ⋊ E`; then `b = a⁻¹x ∈ M'`
(both factors lie in the normal `M'`), so `b ∈ E ⊓ M' ≤ E'` by `inf_derivedInG_le_derivedInG`,
hence `x = a·b ∈ M_σ ⊔ E'`. -/
theorem derivedInG_eq_Msigma_sup_derivedInG_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M ⊔ derivedInG E := by
  classical
  have hM := h.mem_maximal
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  refine le_antisymm (fun x hx => ?_) (sup_le hMσM' ?_)
  · have hxM : x ∈ M := Subgroup.map_subtype_le _ hx
    haveI : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hsuptop : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) h.E_le,
        h.E_compl_sup, Subgroup.subgroupOf_self]
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsuptop ▸ Subgroup.mem_top (⟨x, hxM⟩ : ↥M))
    have hs : (a : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := Subgroup.mem_subgroupOf.mp ha
    have he : (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hb
    have hse : (a : G) * (b : G) = x := by
      have hh := congrArg Subtype.val hab; simpa using hh
    have hbM' : (b : G) ∈ derivedInG M := by
      have hbeq : (b : G) = (a : G)⁻¹ * x := by rw [← hse]; group
      rw [hbeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMσM' hs)) hx
    have hbdE : (b : G) ∈ derivedInG E :=
      h.inf_derivedInG_le_derivedInG (Subgroup.mem_inf.mpr ⟨he, hbM'⟩)
    rw [← hse]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right hbdE)
  · rw [show derivedInG E = ⁅E, E⁆ from Subgroup.map_subtype_commutator E,
      show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono h.E_le h.E_le

/-- **part (h), degenerate case `K = E`** (BG 14.7(8), mmd L4061 with `U = 1`): if the Hall
`κ(M)`-subgroup `K` equals the whole `σ(M)'`-complement `E` (the case `κ(M) ∩ τ₃(M) ≠ ∅` of
Proposition 14.2(a), or `E₂E₃ = 1`), then `E = K` is cyclic, so `E' = 1` and `M' = M_σ`;
the `M_σ ⋊ E` structure makes `K = E` a complement of `M' = M_σ`. -/
theorem typeP_derivedInG_complement_of_eq_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ K : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hKE : K = E) [IsCyclic ↥K] :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) := by
  classical
  -- `E = K` is cyclic, hence abelian, so `E' = ⁅E,E⁆ = ⊥`.
  have hEbot : derivedInG E = ⊥ := by
    rw [← hKE, show derivedInG K = ⁅K, K⁆ from Subgroup.map_subtype_commutator K]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
    letI : CommGroup ↥K := IsCyclic.commGroup
    refine Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥K) (⟨x, hx⟩ : ↥K))
  -- `M' = M_σ ⊔ E' = M_σ`.
  have hM'eq : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG h, hEbot, sup_bot_eq]
  rw [hM'eq, hKE]
  exact h.isComplement'_subgroupOf

/-- **BG Theorem 14.7(h) core, `M'` complements `K`** (mmd L4061): for a type-`P` maximal `M`
with Hall `κ(M)`-subgroup `K` *cyclic* (the counting collapse `n = 1` of Theorem 14.7 makes
`Z = K × K*` cyclic, hence `K`), the derived subgroup `M' = [M,M]` is a complement of `K` in `M`.

By Proposition 14.2(a): take a §12 `E`-setup with `K ≤ E`.  If `κ(M) ∩ τ₃(M) ≠ ∅` then `K = E`
(`typeP_derivedInG_complement_of_eq_complement`).  Otherwise `κ(M) ⊆ τ₁(M)`; conjugate so `K = E₁`,
and (when `E₂E₃ = 1`) again `K = E`, or (`E₂E₃ ≠ 1`) `E = K ⋉ U` is Frobenius with `U = E₂E₃ = E'`
(`U = [U,K]` by the coprime regular action `le_commutator_of_coprime_inf_centralizer_eq_bot`), so
`M' = M_σ ⊔ U`; coprimality (`κ` vs `σ ∪ τ₂ ∪ τ₃`) gives `M' ⊓ K = 1`, and `U ⋊ K = E`,
`M_σ ⋊ E = M` give `M' · K = M`. -/
theorem typeP_derivedInG_isComplement_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) := by
  classical
  -- `K` is a `σ(M)'`-subgroup (a Hall `κ(M)`-subgroup, and `κ(M) ⊆ σ(M)'`).
  have hK_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) K := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hp
    exact kappa_subset_sigmaCompl (hK.1 p hp)
  obtain ⟨E, E₁, E₂, E₃, hsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hM hKM hK_pi
  by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
  · -- Case `κ(M) ∩ τ₃(M) ≠ ∅`: `K = E`.
    obtain ⟨p, hpmem⟩ := hτ3
    rw [Set.mem_inter_iff] at hpmem
    obtain ⟨hpκ, hpτ3⟩ := hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors ((mem_tau3_iff M p).mp hpτ3).2.1
    obtain ⟨hE3ne, hreg⟩ := E3_not_regular_of_mem_kappa_tau3 hG hsetup hp hpκ hpτ3
    obtain ⟨hE1ne, hEeq, hEprime, hEnorm⟩ := E3_not_regular_consequences hG hsetup hE3ne hreg
    obtain ⟨x, hxE3, hxne, hxC⟩ : ∃ x ∈ E₃, x ≠ 1 ∧
        OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hreg fun y hy hy1 => hcon y hy hy1
    have hEpi : Ch03.Subgroup.IsPiGroup (kappa M) (E.subgroupOf M) := by
      intro q hq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv] at hq
      exact mem_kappa_of_mem_primeFactors_card_E hG hsetup hEprime hxE3 hxne hxC hq
    have hEdvdK : Nat.card ↥E ∣ Nat.card ↥K := by
      have hd := hK.card_dvd_of_isPiGroup hEpi
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hd
    have hKEeq : K = E :=
      Subgroup.eq_of_le_of_card_ge hKE (Nat.dvd_antisymm hEdvdK (Subgroup.card_dvd_of_le hKE)).le
    exact typeP_derivedInG_complement_of_eq_complement hG hsetup hKEeq
  · -- Case `κ(M) ⊆ τ₁(M)`: conjugate the setup so its `E₁` is `K`.
    haveI hMsolv : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    have hκτ1 : ∀ p ∈ kappa M, p ∈ tau1 M := fun p hpκ =>
      (kappa_subset_tau1_union_tau3 hpκ).resolve_right
        (fun hpτ3 => hτ3 ⟨p, Set.mem_inter hpκ hpτ3⟩)
    obtain ⟨p₀, hp₀κ⟩ := hP
    obtain ⟨hE1ne, hE1nonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG hsetup
      (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
    have hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := E1_actsPrime hG hsetup hE1ne
    have hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥ :=
      Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hE1prime (le_refl E₁) hE1nonreg
    have hE1HallκE : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf E) :=
      ⟨fun p hp => mem_kappa_of_mem_primeFactors_card_E1 hG hsetup hE1prime hCE1
          (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₁_le).toEquiv] at hp),
        fun p hp hpκ => hsetup.E₁_hall.2 p hp (hκτ1 p hpκ)⟩
    have hE1Hallκ : Ch03.IsHallSubgroup (kappa M) (E₁.subgroupOf M) :=
      hallPiece_isHall_in_M hG hsetup hsetup.E₁_le hE1HallκE kappa_subset_sigmaCompl
    obtain ⟨w, hwM, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv
      (hsetup.E₁_le.trans hsetup.E_le) hKM hE1Hallκ hK
    have h' := SubgroupESetup.conj' hsetup hwM
    rw [hw] at h'
    set Ebar := MulAut.conj w • E with hEbardef
    set Ebar₂ := MulAut.conj w • E₂ with hEbar₂def
    set Ebar₃ := MulAut.conj w • E₃ with hEbar₃def
    -- `h' : SubgroupESetup M Ebar K Ebar₂ Ebar₃`.
    by_cases hUbot : (Ebar₂ ⊔ Ebar₃ : Subgroup G) = ⊥
    · -- `Ebar = K`, so `M' = M_σ` and `K = Ebar` complements it.
      have hEbarK : K = Ebar := by
        have hsup := h'.eq_sup hG
        rw [sup_assoc, hUbot, sup_bot_eq] at hsup
        exact hsup.symm
      exact typeP_derivedInG_complement_of_eq_complement hG h' hEbarK
    · -- `E = K ⋉ U` is a Frobenius group with `U = Ebar₂ ⊔ Ebar₃ ≠ 1`, and `U = E' = [E,E]`.
      have hUleE : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ Ebar := sup_le h'.E₂_le h'.E₃_le
      have hKleEbar : K ≤ Ebar := h'.E₁_le
      obtain ⟨hKne, hKnonreg⟩ := E1_not_regular_of_mem_kappa_tau1 hG h'
        (prime_of_mem_kappa hp₀κ) hp₀κ (hκτ1 p₀ hp₀κ)
      have hKprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K := E1_actsPrime hG h' hKne
      have hKstar' : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ :=
        Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular hKprime (le_refl K) hKnonreg
      have hfrob := isFrobeniusGroup_E_of_caseTau1 hG h' hKne hKstar' hτ3 hUbot
      have hcompl_Ebar : ((Ebar₂ ⊔ Ebar₃).subgroupOf Ebar).IsComplement' (K.subgroupOf Ebar) :=
        hfrob.isComplement
      -- coprime `|K|`, `|U|` and `U ⊓ C(K) = ⊥` (regular action of `K = E₁` on `U`).
      have hcopKU : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(Ebar₂ ⊔ Ebar₃)) := by
        have hc := (hfrob.coprime_card_kernel_complement).symm
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleEbar).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleE).toEquiv] at hc
      have hCUK : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
        obtain ⟨⟨g₀, hg₀K⟩, hg₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
        have hg₀1 : g₀ ≠ 1 := fun hc => hg₀ne (Subtype.ext hc)
        have hr := actsRegularlyOn_E23_E1_of_caseTau1 hG h' hKne hKstar' hτ3 g₀ hg₀K hg₀1
        rw [fixedByElement_def] at hr
        rw [eq_bot_iff, ← hr]
        exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg₀K))
      -- `U = [K, U] ≤ E' = derivedInG Ebar`.
      haveI hKsolv : IsSolvable ↥K :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective (hKleEbar.trans h'.E_le))
      have hUleE' : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ derivedInG Ebar := by
        have hUcomm : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ ⁅K, Ebar₂ ⊔ Ebar₃⁆ :=
          OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot
            (hKleEbar.trans (h'.E23_normal hG)) hcopKU hCUK
        have hcomm_le : (⁅K, Ebar₂ ⊔ Ebar₃⁆ : Subgroup G) ≤ ⁅Ebar, Ebar⁆ :=
          Subgroup.commutator_mono hKleEbar hUleE
        exact hUcomm.trans (le_of_le_of_eq hcomm_le (Subgroup.map_subtype_commutator Ebar).symm)
      -- `E' = U`: the abstract `commutator_eq_sup` for `Ebar = K ⋉ U` with `K` cyclic.
      have hcommEbar_eq : (derivedInG Ebar).subgroupOf Ebar = commutator ↥Ebar := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective Ebar.subtype_injective]
      have hdEbar : derivedInG Ebar = (Ebar₂ ⊔ Ebar₃ : Subgroup G) := by
        haveI hUnorm : ((Ebar₂ ⊔ Ebar₃).subgroupOf Ebar).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer (h'.E23_normal hG)
        have hUcommE : (Ebar₂ ⊔ Ebar₃).subgroupOf Ebar ≤ commutator ↥Ebar := by
          rw [← hcommEbar_eq]; exact Subgroup.comap_mono hUleE'
        have hsupcomm := commutator_eq_sup_commutator_of_isComplement' hcompl_Ebar hUcommE
        have hKbarbot : ⁅K.subgroupOf Ebar, K.subgroupOf Ebar⁆ = ⊥ := by
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (fun x hx => ?_)
          letI : CommGroup ↥K := IsCyclic.commGroup
          refine Subgroup.mem_centralizer_iff.mpr (fun y hy => Subtype.ext ?_)
          have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
          have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
          have hcm := congrArg Subtype.val (mul_comm (⟨(y : G), hyK⟩ : ↥K) (⟨(x : G), hxK⟩ : ↥K))
          simpa using hcm
        rw [hKbarbot, sup_bot_eq] at hsupcomm
        rw [show derivedInG Ebar = (commutator ↥Ebar).map Ebar.subtype from rfl, hsupcomm,
          Subgroup.map_subgroupOf_eq_of_le hUleE]
      -- `M' = M_σ ⊔ U`.
      have hM'eq : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M ⊔ (Ebar₂ ⊔ Ebar₃) := by
        rw [derivedInG_eq_Msigma_sup_derivedInG_complement hG h', hdEbar]
      have hcommM : (derivedInG M).subgroupOf M = commutator ↥M := by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      have hdEbarM : derivedInG Ebar ≤ derivedInG M := by
        rw [show derivedInG Ebar = ⁅Ebar, Ebar⁆ from Subgroup.map_subtype_commutator Ebar,
          show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
        exact Subgroup.commutator_mono h'.E_le h'.E_le
      have hUleM' : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ≤ derivedInG M := hdEbar ▸ hdEbarM
      -- `M' ⊓ K = ⊥` (coprime `κ` vs `σ ∪ τ₂ ∪ τ₃`, via `M' ⊓ K ≤ E' ⊓ K = U ⊓ K`).
      have hMKbot : derivedInG M ⊓ K = ⊥ := by
        have hle1 : derivedInG M ⊓ K ≤ derivedInG Ebar :=
          (inf_le_inf_left (derivedInG M) hKleEbar).trans
            (by rw [inf_comm]; exact h'.inf_derivedInG_le_derivedInG)
        have hbot2 : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊓ K = ⊥ := by
          rw [inf_comm]; exact Subgroup.inf_eq_bot_of_coprime hcopKU
        exact le_bot_iff.mp ((le_inf (hle1.trans hdEbar.le) inf_le_right).trans hbot2.le)
      -- `M' ⊔ K = M` (`U ⊔ K = Ebar`, `M_σ ⊔ Ebar = M`).
      have hUKsup : (Ebar₂ ⊔ Ebar₃ : Subgroup G) ⊔ K = Ebar := by
        have hsup := hcompl_Ebar.sup_eq_top
        rw [← Subgroup.subgroupOf_sup hUleE hKleEbar] at hsup
        exact le_antisymm (sup_le hUleE hKleEbar) (Subgroup.subgroupOf_eq_top.mp hsup)
      have hMKsup : derivedInG M ⊔ K = M := by
        refine le_antisymm (sup_le (Subgroup.map_subtype_le _) hKM) ?_
        calc M = OddOrder.BG.Ch3.S10.Msigma M ⊔ Ebar := h'.E_compl_sup.symm
          _ ≤ derivedInG M ⊔ K := by
              refine sup_le ((OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM).trans le_sup_left) ?_
              rw [← hUKsup]
              exact sup_le (hUleM'.trans le_sup_left) le_sup_right
      -- Assemble the complement: disjoint + product covers `↥M` (`M'` normal).
      have hderM_le : derivedInG M ≤ M := Subgroup.map_subtype_le _
      rw [hcommM]
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff, ← hcommM,
          show (derivedInG M).subgroupOf M ⊓ K.subgroupOf M
            = (derivedInG M ⊓ K).subgroupOf M from rfl, hMKbot, Subgroup.bot_subgroupOf]
      · have hsuptop : commutator ↥M ⊔ K.subgroupOf M = ⊤ := by
          rw [← hcommM, ← Subgroup.subgroupOf_sup hderM_le hKM, hMKsup, Subgroup.subgroupOf_self]
        rw [← Subgroup.normal_mul, hsuptop, Subgroup.coe_top]

/-- **BG Theorem 14.7** (mmd L3890): type-P duality and the `Z_tilde` TI-set.

For a type-P maximal subgroup `M`, there is a unique nonconjugate type-P partner
`Mstar`.  The two Hall factors `K` and `Kstar` form a cyclic subgroup `Z`,
`Z_tilde` is a TI-set, one of the two partners is type `P2`, and every type-P
maximal subgroup is conjugate to one of the pair.

**Part (h)** (BG 14.7(8), exposed 2026-06-15 for Lane G §15 — issue 8006): `M' = [M,M]` is a
complement of `K` in `M` (`M = K M'`, `K ∩ M' = 1`), with `|M'|`, `|K|` coprime.  BG Cor 15.6
(mmd L4232) and Lemma 15.1 cite this directly; it is surfaced as the two leading conjuncts so
`§15` can apply it without re-deriving κ/τ prime-handling. -/
theorem typeP_duality [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) ∧
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      (Kstar ≤ Mstar ∧ Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
        K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G)) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  classical
  -- A Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of `M` (Hall's theorem in the solvable `M`).
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- The counting collapse `n = 1` makes `Z = K ⊔ K*` cyclic, hence the Hall `κ`-factor `K`
  -- cyclic (subgroup of a cyclic group); this is what Proposition 14.2(a)/part (h) consumes.
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
    exists_partner hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU
  haveI hZcyc : IsCyclic ↥(K ⊔ Kstar) :=
    typeP_Z_isCyclic hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  haveI : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  -- Part (h): `M' = [M,M]` complements `K` in `M` (Proposition 14.2(a): `M' = U M_σ`).
  have hparth : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) :=
    typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  exact ⟨hparth, coprime_card_derived_kappaHall_of_isComplement' hK hparth,
    typeP_partner_existsUnique hG (dummySigmaDecomposition G) hM hP hKM hK hKstar hU⟩

/-- **BG `kappaJ`** (conjugation-invariance of `κ`): `κ(M^g) = κ(M)`.  Each defining condition of
`κ` is conjugation-stable: `τ₁(M) ∪ τ₃(M) = {p | p ∉ σ(M) ∧ r_p(M) = 1}` (with `σ`, `pRank`
invariant), and a rank-one witness `P ≤ M` with `M_σ ⊓ C(P) ≠ 1` transports to `P^{g⁻¹}` (via
`M_σ`, centralizer, and `ℰ_p¹` equivariance).  A prerequisite for the type-`P₁`/`P₂`
conjugation-invariance used in BG Cor 14.12 (`typeP2_neighbor_is_typeF`, `sK_FD`). -/
theorem kappa_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    kappa (MulAut.conj g • M) = kappa M := by
  classical
  -- One inclusion for all `a, N` suffices; the reverse follows with `a := g⁻¹`, `N := M^g`.
  suffices h : ∀ (a : G) (N : Subgroup G), kappa (MulAut.conj a • N) ⊆ kappa N by
    refine le_antisymm (h g M) (fun p hp => ?_)
    have hMeq : MulAut.conj g⁻¹ • (MulAut.conj g • M) = M := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact h g⁻¹ (MulAut.conj g • M) (hMeq.symm ▸ hp)
  intro a N p hp
  obtain ⟨hpp, hτ, P, hPelem, hPN, hPC⟩ := hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hinv : MulAut.conj a⁻¹ • (MulAut.conj a • N) = N := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨hpp, ?_, MulAut.conj a⁻¹ • P, conj_smul_mem_elemAbelianOfRank a⁻¹ hPelem, ?_, ?_⟩
  · -- `p ∈ τ₁(N) ∪ τ₃(N)`: from `hτ` extract `p ∉ σ ∧ r_p = 1`, transport, rebuild.
    have hcommon : p ∉ OddOrder.BG.Ch3.S10.sigma (MulAut.conj a • N) ∧
        pRank ↥(MulAut.conj a • N) p = 1 := by
      rcases hτ with h1 | h3
      · exact ⟨((mem_tau1_iff _ _).mp h1).1, ((mem_tau1_iff _ _).mp h1).2.2⟩
      · exact ⟨((mem_tau3_iff _ _).mp h3).1, ((mem_tau3_iff _ _).mp h3).2.2⟩
    have hσN : p ∉ OddOrder.BG.Ch3.S10.sigma N := by
      have h1 := hcommon.1; rwa [sigma_conj_smul_eq] at h1
    have hpRankN : pRank ↥N p = 1 := by
      have heq : pRank ↥N p = pRank ↥(MulAut.conj a • N) p :=
        pRank_eq_of_mulEquiv
          (Subgroup.equivMapOfInjective N (MulAut.conj a).toMonoidHom (MulAut.conj a).injective)
      rw [heq]; exact hcommon.2
    by_cases hπ : p ∈ (Nat.card ↥(derivedInG N)).primeFactors
    · exact Or.inr ((mem_tau3_iff _ _).mpr ⟨hσN, hπ, hpRankN⟩)
    · exact Or.inl ((mem_tau1_iff _ _).mpr ⟨hσN, hπ, hpRankN⟩)
  · -- `P^{a⁻¹} ≤ N` (apply `conj a⁻¹` to `P ≤ M^a`).
    rw [← hinv]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPN
  · -- `M_σ(N) ⊓ C(P^{a⁻¹}) ≠ ⊥` (apply `conj a⁻¹` to `M_σ(M^a) ⊓ C(P) ≠ ⊥`).
    have hbot : MulAut.conj a⁻¹ • (OddOrder.BG.Ch3.S10.Msigma (MulAut.conj a • N) ⊓
        Subgroup.centralizer (P : Set G)) ≠ ⊥ := by
      rw [Ne, pointwise_smul_eq_bot_iff]; exact hPC
    rwa [Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul,
      show MulAut.conj a⁻¹ • OddOrder.BG.Ch3.S10.Msigma (MulAut.conj a • N)
        = OddOrder.BG.Ch3.S10.Msigma N from by rw [← Msigma_conj_smul, hinv]] at hbot

/-- `π(M) ∖ σ(M)` (`sigmaComplementPrimes`) is conjugation-invariant. -/
theorem sigmaComplementPrimes_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    sigmaComplementPrimes (MulAut.conj g • M) = sigmaComplementPrimes M := by
  unfold sigmaComplementPrimes piSet
  rw [card_pointwise_smul, sigma_conj_smul_eq]

/-- **Type-`P` is conjugation-invariant** (`kappa_conj_smul`). -/
theorem isTypeP_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP (MulAut.conj g • M) ↔ IsTypeP M := by
  unfold IsTypeP; rw [kappa_conj_smul]

/-- **Type-`P₁` is conjugation-invariant**. -/
theorem isTypeP1_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP1 (MulAut.conj g • M) ↔ IsTypeP1 M := by
  unfold IsTypeP1
  rw [kappa_conj_smul, sigmaComplementPrimes_conj_smul, isTypeP_conj_smul]

/-- **A normal Hall subgroup is the unique Hall subgroup of its primes** (finite solvable group):
two Hall `π`-subgroups are conjugate (`hall_C`), and a normal one is fixed by conjugation, so they
coincide.  Used to pin the Theorem D normal complement `R(x)` (a normal Hall complement in `C_G(x)`)
to the canonical signalizer `Rsub`. -/
theorem eq_of_isHall_of_normal {K : Type*} [Group K] [Finite K] [IsSolvable K] {π : Set ℕ}
    {H₁ H₂ : Subgroup K} (hH₁ : Ch03.IsHallSubgroup π H₁) (hH₂ : Ch03.IsHallSubgroup π H₂)
    (hN : H₁.Normal) : H₁ = H₂ := by
  haveI := hN
  obtain ⟨g, hg⟩ := Ch03.hall_C hH₁ hH₂
  rw [← hg]
  exact (Subgroup.Normal.conj_smul_eq_self g H₁).symm

/-- **κ-Hall data transfers under conjugation of the ambient maximal**: if `conj g • N = M` and
`KN.subgroupOf N` is a Hall `κ(N)`-subgroup, then `(conj g • KN).subgroupOf M` is a Hall
`κ(M)`-subgroup.  Conjugation by `g` restricts to a `↥N ≃ ↥M` preserving both `Nat.card` and the
index, and `κ` is conjugation-invariant.  This is the fix-`W` data step: it lets a conjugate
type-`P` maximal's `Ẑ` be related to a fixed reference `Ẑ`. -/
theorem isHall_kappa_subgroupOf_conj [Finite G] (g : G) {M N KN : Subgroup G}
    (hg : MulAut.conj g • N = M) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N)) :
    Ch03.IsHallSubgroup (kappa M) ((MulAut.conj g • KN).subgroupOf M) := by
  have hkap : kappa M = kappa N := by rw [← hg, kappa_conj_smul]
  have hle : MulAut.conj g • KN ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKNN
  -- `Nat.card` is conjugation-invariant; the two `subgroupOf`s have equal card (both `= Nat.card KN`).
  have hcardKN : Nat.card ↥(MulAut.conj g • KN) = Nat.card ↥KN := by
    rw [Subgroup.pointwise_smul_def]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hcardamb : Nat.card ↥(MulAut.conj g • N) = Nat.card ↥N := by
    rw [Subgroup.pointwise_smul_def]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).toEquiv).symm
  have hcard : Nat.card ↥((MulAut.conj g • KN).subgroupOf M) = Nat.card ↥(KN.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKNN).toEquiv, hcardKN]
  -- the indices agree, via `index · card = card ambient` and the card equalities above.
  have hidx : ((MulAut.conj g • KN).subgroupOf M).index = (KN.subgroupOf N).index := by
    have hMrel := ((MulAut.conj g • KN).subgroupOf M).index_mul_card
    have hNrel := (KN.subgroupOf N).index_mul_card
    have hMN : Nat.card ↥M = Nat.card ↥N := by rw [← hg]; exact hcardamb
    rw [hcard, hMN] at hMrel
    rw [← hNrel] at hMrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hMrel
  unfold Ch03.IsHallSubgroup at hKN ⊢
  rw [hkap, hcard, hidx]; exact hKN

/-- **fix-`W` threading**: two conjugate type-`P` maximals `N ~ M` carry `Ẑ`'s with the same
`G`-conjugacy-class closure.  Concretely, if `N` and `M` carry Theorem 14.7 data
`(KN, KstarN)` resp. `(K, Kstar)` and `N` is `G`-conjugate to `M`, then
`𝒞_G(zTilde KN KstarN) = 𝒞_G(zTilde K Kstar)`.  The conjugator `g` (`conj g • N = M`) is corrected
by a Hall conjugacy `w ∈ M` so that `conj (w*g)` carries `N`'s data exactly onto `M`'s; the
`conjClassSet` is then conjugation-invariant via `conjClassSet_zTilde_conj_eq`. -/
theorem conjClassSet_zTilde_eq_of_isConjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M N K Kstar KN KstarN : Subgroup G}
    (hMmax : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hNmax : N ∈ maximalSubgroups G) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hKstarN : KstarN = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G))
    (hconj : IsConjugateSubgroup N M) :
    conjClassSet (zTilde KN KstarN) = conjClassSet (zTilde K Kstar) := by
  obtain ⟨g, hg⟩ := hconj
  have hle : MulAut.conj g • KN ≤ M := by
    rw [← hg]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKNN
  have hHallM : Ch03.IsHallSubgroup (kappa M) ((MulAut.conj g • KN).subgroupOf M) :=
    isHall_kappa_subgroupOf_conj g hg hKNN hKN
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hMmax
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hle hKM hHallM hK
  -- `conj (w*g)` carries `N`'s `κ`-Hall and ambient maximal exactly onto `M`'s.
  have hKeq : MulAut.conj (w * g) • KN = K := by rw [map_mul, mul_smul]; exact hw
  have hMN : MulAut.conj (w * g) • N = M := by
    rw [map_mul, mul_smul, hg]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwM)
  -- hence it carries `KstarN = N_σ ∩ C(KN)` onto `Kstar = M_σ ∩ C(K)`.
  have hKstareq : MulAut.conj (w * g) • KstarN = Kstar := by
    rw [hKstarN, Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul, hKeq, hKstar]
    congr 1
    rw [← Msigma_conj_smul, hMN]
  -- `conjClassSet` is conjugation-invariant on `Ẑ`.
  calc conjClassSet (zTilde KN KstarN)
      = conjClassSet (zTilde (MulAut.conj (w * g) • KN) (MulAut.conj (w * g) • KstarN)) :=
        (conjClassSet_zTilde_conj_eq (w * g) KN KstarN).symm
    _ = conjClassSet (zTilde K Kstar) := by rw [hKeq, hKstareq]

/-- **fix-`W`** (BG Cor 14.8 packaging): for a reference type-`P` maximal `M` (with Theorem 14.7
data `K, K*, U`) and *any* type-`P` maximal `N` (with data `KN, KstarN`), the `Ẑ` of `N` has the
same `G`-conjugacy-class closure as the fixed `Ẑ(M) = zTilde K K*`.  Every type-`P` `N` is
`G`-conjugate to `M` or to its partner `M*` (`typeP_covering`); the `M`-class lands on `W` by
`conjClassSet_zTilde_eq_of_isConjugate`, and the `M*`-class lands on `zTilde K* K = zTilde K K*`
(`typeP_partner_structure` supplies `M*`'s data `(K*, K)`, then `zTilde_comm`). -/
theorem conjClassSet_zTilde_eq_fixed_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U N KN KstarN : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hNmax : N ∈ maximalSubgroups G) (hNP : IsTypeP N) (hKNN : KN ≤ N)
    (hKN : Ch03.IsHallSubgroup (kappa N) (KN.subgroupOf N))
    (hKstarN : KstarN = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer (KN : Set G)) :
    conjClassSet (zTilde KN KstarN) = conjClassSet (zTilde K Kstar) := by
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
    exists_partner hG (genuineSigmaDecomposition hG) hM hP hKM hK hKstar hU
  obtain ⟨hMstarmax, hMstarP, hKstarMstar, hKstar_hall, hKeq⟩ :=
    typeP_partner_structure hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  rcases typeP_covering hG hM hP hKM hK hKstar hU hMstarmem hMstarne hpart hNmax hNP with
    hNM | hNMstar
  · exact conjClassSet_zTilde_eq_of_isConjugate hG hM hKM hK hKstar hNmax hKNN hKN hKstarN hNM
  · rw [conjClassSet_zTilde_eq_of_isConjugate hG hMstarmax hKstarMstar hKstar_hall hKeq
      hNmax hKNN hKN hKstarN hNMstar, zTilde_comm]

/-- **Type-`P` data constructor**: every maximal subgroup `M` carries the Theorem 14.7 data — a
Hall `κ(M)`-subgroup `K ≤ M`, the swap `K* = M_σ ∩ C_G(K)`, and a Hall `(κ ∪ σ)ᶜ`-subgroup `U` —
obtained from Hall's theorem in the solvable `↥M`.  This is the missing constructor that lets the
family-level corollaries (14.8) feed `exists_partner` / `typeP_covering` from a bare
`M ∈ maximalTypePFamily`. -/
theorem exists_typeP_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ K Kstar U : Subgroup G, K ≤ M ∧
      Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M) ∧
      Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ∧
      Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) := by
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
  obtain ⟨HK, hHK⟩ := Ch03.hall_E_exists (G := ↥M) (kappa M)
  obtain ⟨HU, hHU⟩ :=
    Ch03.hall_E_exists (G := ↥M) ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  refine ⟨HK.map M.subtype,
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ((HK.map M.subtype : Subgroup G) : Set G),
    HU.map M.subtype, Subgroup.map_subtype_le _, ?_, rfl, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hHK
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hHU

/-- **BG Corollary 14.8** (mmd L4065): the type-`P₁` maximal subgroups, if any, are all
conjugate in `G`; and if the type-`P` family is nonempty it consists of exactly two conjugacy
classes of maximal subgroups (`M` and its nonconjugate partner `M*` from Theorem 14.7).

Follows directly from Theorem 14.7(f),(g) (gated on §13 via Prop 14.2 / Theorem 14.7). -/
theorem typeP1_conjugate_and_typeP_twoClasses [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (∀ M ∈ maximalTypeP1Family G, ∀ N ∈ maximalTypeP1Family G, IsConjugateSubgroup M N) ∧
    ((maximalTypePFamily G).Nonempty →
      ∃ M ∈ maximalTypePFamily G, ∃ Mstar ∈ maximalTypePFamily G,
        ¬ IsConjugateSubgroup M Mstar ∧
        ∀ H ∈ maximalTypePFamily G,
          IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  refine ⟨fun M hMfam N hNfam => ?_, fun hne => ?_⟩
  · -- **Part 1** (`𝓜_{P₁}` is a single class): two type-`P₁` maximals `M`, `N` are conjugate.
    -- The Theorem 14.7 partner `M*` of `M` is type-`P₂` (`isTypeP2_or_isTypeP2_partner`, since `M`
    -- is type-`P₁` hence not type-`P₂`); the covering puts `N ~ M` or `N ~ M*`, and `N ~ M*` would
    -- make `M*` type-`P₁` (conjugation-invariant), contradicting type-`P₂`.  So `N ~ M`.
    obtain ⟨hMmax, hMP1⟩ := hMfam
    obtain ⟨hNmax, hNP1⟩ := hNfam
    obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hMmax
    obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
      exists_partner hG (genuineSigmaDecomposition hG) hMmax hMP1.1 hKM hK hKstar hU
    have hMstarP2 : IsTypeP2 Mstar := by
      rcases isTypeP2_or_isTypeP2_partner hG (genuineSigmaDecomposition hG) hMmax hMP1.1 hKM hK
        hKstar hU hpart with hM2 | hMstar2
      · exact absurd ⟨hMP1, hM2⟩ not_isTypeP1_and_isTypeP2
      · exact hMstar2
    rcases typeP_covering hG hMmax hMP1.1 hKM hK hKstar hU hMstarmem hMstarne hpart hNmax hNP1.1
      with hNM | hNMstar
    · exact hNM.symm
    · exfalso
      obtain ⟨a, ha⟩ := hNMstar
      exact not_isTypeP1_and_isTypeP2
        ⟨ha ▸ (isTypeP1_conj_smul a N).mpr hNP1, hMstarP2⟩
  · -- **Part 2** (`𝓜_P` = two conjugacy classes): the partner pair `(M, M*)` of Theorem 14.7,
    -- with `typeP_covering` placing every type-`P` `H` in one of the two classes.
    obtain ⟨M, hMmax, hMP⟩ := hne
    obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hMmax
    obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
      exists_partner hG (genuineSigmaDecomposition hG) hMmax hMP hKM hK hKstar hU
    obtain ⟨hMstarmax, hMstarP, _⟩ :=
      typeP_family_member_data hG hMmax hMP hKM hK hKstar hU hMstarmem
    refine ⟨M, ⟨hMmax, hMP⟩, Mstar, ⟨hMstarmax, hMstarP⟩, ?_, ?_⟩
    · exact typeP_family_pairwise_nonconjugate hG hMmax hMP hKM hK hKstar hU (Or.inl rfl)
        hMstarmem (Ne.symm hMstarne)
    · rintro H ⟨hHmax, hHP⟩
      exact typeP_covering hG hMmax hMP hKM hK hKstar hU hMstarmem hMstarne hpart hHmax hHP

/-- **BG Corollary 14.9** (mmd L3997): `G^#` is the disjoint union of the conjugacy pieces
`𝒞_G(M̃ᵢ)` over class representatives `Mᵢ ∈ 𝓜` — together with one extra `𝒞_G(Ẑ)` piece when
`𝓜_𝓟` is nonempty.

**Faithfulness note (2026-06-14):** the Lean surface covers by `sigmaConjugacySaturation =
𝒞_G(M_σ^#)` instead of BG's `𝒞_G(M̃)` (see `sigmaSharp`). Because `M_σ^# ⊊ M̃`, covering `G^#`
by the *smaller* pieces is **stronger than — and false relative to — BG**: the `ℓ_σ = 2`
twisted elements `x x'` (`x' ∈ R(x)^#`) lie in some `𝒞_G(M̃ᵢ)` but in no `𝒞_G(M_σ^#ⱼ)`, so the
covering fails for them. A faithful statement needs the (gated) `M̃`; do not prove this
surface as-is. See `notes/bg/s14_typeP_counting.md`. -/
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

/-- **`Ẑ` elements have `σ`-length at most two** (the type-P exceptional half of BG Cor 14.10).  A
`z ∈ Ẑ = zTilde Kref Kstarref = (Kref ⊔ Kstarref) ∖ (Kref ∪ Kstarref)` factors as `z = k·k*` with
`k* ∈ Kstarref ⊆ M_σ(Mref)#` (a `σ(Mref)`-element, so `ℓ_σ(k*) = 1`) and `k ∈ Kref` a nonidentity
`κ(Mref)`-element; since `Kref` consists of `σ(Mref*)`-elements for the non-conjugate partner `Mref*`
(type-P duality), `sigma_cover_decomposition` gives the two-element `σ`-decomposition `{k, k*}`.

**Proof recipe (verified 2026-07-01, no deep gap — only a mechanical split remains):**
`typeP_duality hG hMref hMPref hKMref hKref hKstarref` supplies the partner `Mstar` with
`hK_eq : Kref = M_σ(Mstar) ⊓ C(Kstar)` (so `Kref ≤ M_σ(Mstar)` by `inf_le_left` — the partner-`σ`
membership is *immediate*, not a residual), `hnc : ¬ IsConjugateSubgroup Mref Mstar`, and `hZcyc`
(`K ⊔ K*` cyclic).  Then `z ∈ Ẑ` splits as `z = k·k*` (`k ∈ Kref ≤ M_σ(Mstar)#`,
`k* ∈ Kstarref ≤ M_σ(Mref)`, commuting, both `≠ 1`), and `sigma_cover_decomposition hG hMstarmax
hMref (·) (Kref ≤ M_σ Mstar applied to k) hk1 (Kstarref ≤ M_σ Mref applied to k*) hcomm` gives
`sigmaDecomposition (k·k*) = insert k ({k*} \ {1})`, of `ncard ≤ 2`.

**Only mechanical gap (`sorry`):** the `k·k*` split — `z ∈ (Kref ⊔ Kstarref)` with `Kstarref`
central there.  `Subgroup.mem_sup` (CommGroup `↥(Kref⊔Kstarref)` via `hZcyc.commGroup`) hit an
instance diamond; redo via `Subgroup.mem_sup_of_normal_left` after establishing
`(Kstarref.subgroupOf (Kref⊔Kstarref)).Normal` from centrality.  The `M̃`-piece
(`sigmaLength_le_two_of_mem_Mtilde`) and the Cor 14.10 cover/conjugation plumbing are sorry-free. -/
theorem sigmaLength_le_two_of_mem_zTilde_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {z : G} (hz : z ∈ zTilde Kref Kstarref) :
    sigmaLength z ≤ 2 := by
  classical
  -- The dual partner `Mstar` (Theorem 14.7 duality): `K = M*_σ ⊓ C(K*)` (so `K ≤ M*_σ`) and
  -- `M` not conjugate to `M*`.
  obtain ⟨_, _, hExU⟩ := typeP_duality hG hMref hMPref hKMref hKref hKstarref
  obtain ⟨Mstar, ⟨hMstarmax, _, hnc, ⟨_, _, hK_eq⟩, _, _, _, _⟩, _⟩ := hExU
  have hKMsig : Kref ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := hK_eq.trans_le inf_le_left
  have hKstarMsig : Kstarref ≤ OddOrder.BG.Ch3.S10.Msigma Mref := hKstarref.trans_le inf_le_left
  -- Unpack `z ∈ Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`.
  rw [zTilde, Set.mem_sdiff, Set.mem_union] at hz
  obtain ⟨hzW, hznot⟩ := hz
  have hzW' : z ∈ Kref ⊔ Kstarref := SetLike.mem_coe.mp hzW
  -- `K ◁ (K ⊔ K*)` (`K*` centralises `K`), so the split `z = k·k*` exists (no `CommGroup` needed).
  haveI hKrefnorm : (Kref.subgroupOf (Kref ⊔ Kstarref)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer
      (le_trans (hKstarref.trans_le inf_le_right)
        (Subgroup.centralizer_le_normalizer (↑Kref : Set G)))
  have hsplit : (⟨z, hzW'⟩ : ↥(Kref ⊔ Kstarref)) ∈
      (Kref.subgroupOf (Kref ⊔ Kstarref)) ⊔ (Kstarref.subgroupOf (Kref ⊔ Kstarref)) := by
    rw [codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup Kref Kstarref)]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_left] at hsplit
  obtain ⟨a, ha, b, hb, hab⟩ := hsplit
  have hkK : (a : G) ∈ Kref := Subgroup.mem_subgroupOf.mp ha
  have hksK : (b : G) ∈ Kstarref := Subgroup.mem_subgroupOf.mp hb
  have hzkk : z = (a : G) * (b : G) := by
    have h := congrArg (Subgroup.subtype (Kref ⊔ Kstarref)) hab
    simpa using h.symm
  have hk1 : (a : G) ≠ 1 := by
    rintro h0
    exact hznot (Or.inr (by rw [hzkk, h0, one_mul]; exact SetLike.mem_coe.mpr hksK))
  have hks1 : (b : G) ≠ 1 := by
    rintro h0
    exact hznot (Or.inl (by rw [hzkk, h0, mul_one]; exact SetLike.mem_coe.mpr hkK))
  have hksC : (b : G) ∈ Subgroup.centralizer (↑Kref : Set G) :=
    (hKstarref.trans_le inf_le_right) hksK
  have hcomm : Commute (a : G) (b : G) :=
    Subgroup.mem_centralizer_iff.mp hksC (a : G) (SetLike.mem_coe.mpr hkK)
  have hMN : ¬ ∃ g : G, MulAut.conj g • Mstar = Mref := fun h => hnc (IsConjugateSubgroup.symm h)
  -- `z = k·k*` with `k ∈ M*_σ#`, `k* ∈ M_σ`, `M*`/`M` non-conjugate: `sigma_cover_decomposition`.
  have hdecomp := sigma_cover_decomposition hG hMstarmax hMref hMN (hKMsig hkK) hk1
    (hKstarMsig hksK) hcomm
  rw [sigmaLength, hzkk, hdecomp]
  have h1 : (({(b : G)} : Set G) \ {1}).ncard ≤ 1 :=
    (Set.ncard_le_ncard Set.sdiff_subset (Set.finite_singleton _)).trans
      (le_of_eq (Set.ncard_singleton _))
  calc (insert (a : G) (({(b : G)} : Set G) \ {1})).ncard
      ≤ (({(b : G)} : Set G) \ {1}).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ 2 := by omega

/-! ### BG Lemma 14.11 — phase 1: `Q ⊄ F(E) ⟹ q ∈ τ₁(M)` and `C_{M_σ}(Q) = 1`

The proof of Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting` below) first locates the prime
`q` in the τ-partition and pins down its `M_σ`-centralizer.  These first steps are factored as
reusable lemmas; the remaining structure (the cyclic-normal `⁅E,Q⁆`, `τ₂(M) ≠ ∅`, and the
`M*`-dichotomy) is recorded in `issues/7007`. -/

/-- Build a `SubgroupESetup` on a *given* `M_σ`-complement `E` (converting the `IsComplement'`
hypothesis to the `M_σ ⊓ E = ⊥`, `M_σ ⊔ E = M` form expected by `subgroupESetup_of_complement`). -/
theorem esetup_of_isComplement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hEM : E ≤ M) :
    ∃ E₁ E₂ E₃ : Subgroup G, SubgroupESetup M E E₁ E₂ E₃ := by
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hinf : OddOrder.BG.Ch3.S10.Msigma M ⊓ E = ⊥ := by
    have hd := hE.disjoint
    rw [disjoint_iff] at hd
    have h2 : (OddOrder.BG.Ch3.S10.Msigma M ⊓ E).subgroupOf M = ⊥ := by
      have he : (OddOrder.BG.Ch3.S10.Msigma M ⊓ E).subgroupOf M
          = (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊓ E.subgroupOf M :=
        Subgroup.comap_inf _ _ M.subtype
      rw [he]; exact hd
    have h3 := congrArg (Subgroup.map M.subtype) h2
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_of_left_le hMσM), Subgroup.map_bot] at h3
  have hsup : OddOrder.BG.Ch3.S10.Msigma M ⊔ E = M := by
    have hs := hE.sup_eq_top
    have h3 := congrArg (Subgroup.map M.subtype) hs
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hMσM,
      Subgroup.map_subgroupOf_eq_of_le hEM, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h3
    exact h3
  exact subgroupESetup_of_complement hG hM hEM hinf hsup

/-- BG Lemma 14.11 step S1: `q ∉ τ₂(M)`.  A rank-2 elem abelian `B ∈ ℰ_q²(E)` is normal in `E`
(Cor 12.6(a)) hence `≤ F(E)`; line-membership forces `Q ≤ B ≤ F(E)`, contradicting `Q ⊄ F(E)`. -/
theorem typeF_complement_q_notMem_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∉ tau2 M := by
  intro hτ2
  obtain ⟨B, hB, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetup hτ2
  obtain ⟨⟨hENB, hline⟩, _⟩ := elemAb_normal_in_E_of_tau2 hG hsetup hτ2 hB hBE
  have hQB : Q ≤ B := (hline Q hQ).mp hQE
  have hBnorm : (B.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mpr hENB
  have hBpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) B := by
    intro p hp
    rw [hB.2, Nat.primeFactors_prime_pow (by norm_num) (Fact.out : q.Prime),
      Finset.mem_singleton] at hp
    exact hp
  have hBF : B ≤ OddOrder.BG.Ch2.S08.fittingInG E :=
    OddOrder.BG.Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hBE hBnorm hBpi
  exact hQF (hQB.trans hBF)

/-- BG Lemma 14.11 step S2: `q ∉ τ₃(M)`.  The τ₃-Hall `E₃` is cyclic, normal in `E`, hence `≤ F(E)`
(`E3_le_fittingInG`); a `q`-subgroup with `q ∈ τ₃` lands in `E₃`, so `Q ≤ E₃ ≤ F(E)`. -/
theorem typeF_complement_q_notMem_tau3 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃)
    (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∉ tau3 M := by
  intro hτ3
  haveI hE₃norm : (E₃.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsetup.E₃_le).mpr (hsetup.E3_normal hG)
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  have hQpiG : Ch03.Subgroup.IsPiGroup (tau3 M) (Q.subgroupOf E) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQcard,
      (Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hτ3
  have hle : Q.subgroupOf E ≤ E₃.subgroupOf E :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hsetup.E₃_hall hQpiG
  have hQE₃ : Q ≤ E₃ := by
    have := Subgroup.map_mono (f := E.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hQE,
      Subgroup.map_subgroupOf_eq_of_le hsetup.E₃_le] at this
  exact hQF (hQE₃.trans (E3_le_fittingInG hG hsetup))

/-- BG Lemma 14.11 steps S1–S3 + gap C: `Q ⊄ F(E)` with `M ∈ 𝓜_F` forces `q ∈ τ₁(M)` and
`C_{M_σ}(Q) = 1`.  (`q ∈ π(E) ⊆ σ(M)'` is τ-covered; S1/S2 rule out τ₂/τ₃; a nontrivial
`C_{M_σ}(Q)` would place `q ∈ κ(M) = ∅`.) -/
theorem typeF_complement_q_tau1_and_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ}
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hF : IsTypeF M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    q ∈ tau1 M ∧ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  have hqτ1 : q ∈ tau1 M := by
    rcases hsetup.mem_tau_union_of_mem_primeFactors hG hqpf with (h | h) | h
    · exact h
    · exact absurd h (typeF_complement_q_notMem_tau2 hG hsetup hQ hQE hQF)
    · exact absurd h (typeF_complement_q_notMem_tau3 hG hsetup hQ hQE hQF)
  have hQM : Q ≤ M := hQE.trans hsetup.E_le
  refine ⟨hqτ1, ?_⟩
  by_contra hne
  exact Set.notMem_empty q (hF ▸ (⟨Fact.out, Or.inl hqτ1, Q, hQ, hQM, hne⟩ : q ∈ kappa M))

open scoped IsMulCommutative commutatorElement in
/-- **BG Lemma 14.11, step S5 (degenerate case).**  If `Q ≤ E` is abelian, `R := ⁅E, Q⁆` is
abelian, and `R` centralizes `Q` (equivalently `⁅⁅E, Q⁆, Q⁆ = 1`), then the normal closure
`Q ⊔ R` of `Q` in `E` is abelian and normal in `E`, hence `Q ≤ F(E)`.  This is used to rule out
`⁅⁅E, Q⁆, Q⁆ = 1` when `Q ⊄ F(E)`: the set of `x` with `⁅x, e⁆ ∈ Q ⊔ R` is a subgroup containing
the generators `Q` and `R`, so `Q ⊔ R` is `E`-normal; it is abelian by `R ≤ C_G(Q)`. -/
private theorem Q_le_fittingInG_of_commutator_centralizesQ [Finite G]
    {E Q : Subgroup G} (hQE : Q ≤ E) (hQab : IsMulCommutative ↥Q)
    (hRab : IsMulCommutative ↥(⁅E, Q⁆ : Subgroup G))
    (hC : (⁅E, Q⁆ : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) :
    Q ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
  classical
  set R : Subgroup G := ⁅E, Q⁆ with hRdef
  have hRE : R ≤ E := (Subgroup.commutator_mono le_rfl hQE).trans (Subgroup.commutator_le_self E)
  have hNE : Q ⊔ R ≤ E := sup_le hQE hRE
  have hRnorm : E ≤ Subgroup.normalizer (R : Set G) :=
    hRdef ▸ Ch04.subgroup_le_normalizer_commutator_self E Q
  have hRE_comm : (⁅R, E⁆ : Subgroup G) ≤ R := Ch04.commutator_le_of_le_normalizer hRnorm
  have hC' : Q ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hC
  -- `Q ⊔ R` is normalized by `E`.
  have hEnormN : E ≤ Subgroup.normalizer ((Q ⊔ R : Subgroup G) : Set G) := by
    refine Ch04.le_normalizer_of_commutator_le ?_
    rw [Subgroup.commutator_le]
    intro n hn e he
    let Se : Subgroup G :=
      { carrier := {x | x ∈ (Q ⊔ R : Subgroup G) ∧ ⁅x, e⁆ ∈ (Q ⊔ R : Subgroup G)}
        one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
        mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
          have hid : ⁅a * b, e⁆ = a * ⁅b, e⁆ * a⁻¹ * ⁅a, e⁆ := by
            simp only [commutatorElement_def]; group
          rw [hid]
          exact mul_mem (mul_mem (mul_mem ha.1 hb.2) (inv_mem ha.1)) ha.2⟩
        inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
          have hid : ⁅a⁻¹, e⁆ = a⁻¹ * ⁅a, e⁆⁻¹ * a := by
            simp only [commutatorElement_def]; group
          rw [hid]
          exact mul_mem (mul_mem (inv_mem ha.1) (inv_mem ha.2)) ha.1⟩ }
    have hQSe : Q ≤ Se := fun x hx => ⟨Subgroup.mem_sup_left hx, by
      refine Subgroup.mem_sup_right ?_
      rw [hRdef, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx he⟩
    have hRSe : R ≤ Se := fun x hx => ⟨Subgroup.mem_sup_right hx,
      Subgroup.mem_sup_right (hRE_comm (Subgroup.commutator_mem_commutator hx he))⟩
    exact ((sup_le hQSe hRSe : (Q ⊔ R) ≤ Se) hn).2
  haveI hNnorm : ((Q ⊔ R).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNE).mpr hEnormN
  have hNab : IsMulCommutative ↥(Q ⊔ R : Subgroup G) := by
    refine isMulCommutative_of_le_centralizer ?_
    rw [centralizer_sup_eq]
    exact le_inf (sup_le (le_centralizer_of_le_of_le hQab le_rfl le_rfl) hC)
      (sup_le hC' (le_centralizer_of_le_of_le hRab le_rfl le_rfl))
  haveI : IsMulCommutative ↥(Q ⊔ R : Subgroup G) := hNab
  haveI : Group.IsNilpotent ↥(Q ⊔ R : Subgroup G) := inferInstance
  haveI : Group.IsNilpotent ↥((Q ⊔ R).subgroupOf E) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNE).symm
  have hfit : (Q ⊔ R).subgroupOf E ≤ OddOrder.Isaacs.Ch01.fitting ↥E :=
    Ch01.nilpotent_normal_le_fitting
  have hNfitG : (Q ⊔ R : Subgroup G) ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
    have hmap := Subgroup.map_mono (f := E.subtype) hfit
    rwa [Subgroup.map_subgroupOf_eq_of_le hNE] at hmap
  exact le_sup_left.trans hNfitG

open OddOrder.BG.Ch3.S10 in
/-- **BG Lemma 14.11, steps S4–S7**: under the Lemma 14.11 hypotheses (`M ∈ 𝓜_F`, `E` a
`M_σ`-complement, `q ∈ π(E)`, `Q ∈ ℰ_q¹(E)`, `Q ⊄ F(E)`), there is a nontrivial cyclic subgroup
`K' = ⁅⁅E, Q⁆, Q⁆ ≤ E` that is normal in `M`, contained in `C_G(M_σ)`, has all primes in `τ₂(M)`
(so `τ₂(M) ≠ ∅`), and on which `Q` acts fixed-point-freely (`C_{K'}(Q) = 1`).

`K := ⁅E, Q⁆` is an abelian (Cor 12.10(b)) `q'`-subgroup of `M` normalized by `Q`; Proposition
10.11(d) makes `K' := ⁅K, Q⁆` cyclic, normal in `M`, and contained in `C_G(M_σ)`.  If `K' = 1`
then `⁅E, Q⁆ ≤ C_G(Q)` and `Q ≤ F(E)` (the S5 helper), contradicting `Q ⊄ F(E)`; so `K' ≠ 1`.
A prime `p ∈ π(K')` lies in `τ₂(M)`: otherwise `p ∈ τ₁(M) ∪ τ₃(M)` has `r_p(M) = 1`, and a line
`A ∈ ℰ_p¹` of `K' ≤ C_G(M_σ)` would have `C_{M_σ}(A) = M_σ ≠ 1`, contradicting Lemma 14.1.  The
`C_{K'}(Q) = 1` fixed-point-freeness comes from the coprime identity `⁅K', Q⁆ = K'` (BG **G** 8.5.4,
`commutator_commutator_right_eq` in `↥E`) and the coprime complement `fitting_coprime_abelian_decomp`. -/
theorem exists_typeF_complement_cyclic_commutator [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ Q : Subgroup G} {q : ℕ}
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hF : IsTypeF M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ K' : Subgroup G,
      K' ≤ E ∧ K' ≠ ⊥ ∧ IsCyclic ↥K' ∧
      K' ≤ Subgroup.centralizer (Msigma M : Set G) ∧
      M ≤ Subgroup.normalizer (K' : Set G) ∧
      (∀ p ∈ (Nat.card ↥K').primeFactors, p ∈ tau2 M) ∧
      Subgroup.centralizer (Q : Set G) ⊓ K' = ⊥ := by
  classical
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  obtain ⟨hqτ1, hCQ⟩ := typeF_complement_q_tau1_and_centralizer hG hsetup hF hq hQ hQE hQF
  have hQM : Q ≤ M := hQE.trans hsetup.E_le
  -- `K := ⁅E, Q⁆` is an abelian `q'`-subgroup of `M`, `σ(M)'`-subgroup.
  set K : Subgroup G := ⁅E, Q⁆ with hKdef
  have hK_le_derivedE : K ≤ derivedInG E := by
    rw [hKdef, show derivedInG E = ⁅E, E⁆ from Subgroup.map_subtype_commutator E]
    exact Subgroup.commutator_mono le_rfl hQE
  have hKE : K ≤ E := hK_le_derivedE.trans (Subgroup.map_subtype_le _)
  have hKM : K ≤ M := hKE.trans hsetup.E_le
  have hK_le_derivedM : K ≤ derivedInG M := by
    rw [hKdef, show derivedInG M = ⁅M, M⁆ from Subgroup.map_subtype_commutator M]
    exact Subgroup.commutator_mono hsetup.E_le hQM
  have hKab : IsMulCommutative ↥K :=
    isMulCommutative_of_le ((nilpotent_sigmaComplement_abelian hG hsetup).2.1.2) hK_le_derivedE
  have hKσ' : Subgroup.IsPiSubgroup (sigma M)ᶜ K := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hKE), Nat.card_pos.ne'⟩
    rcases hsetup.mem_tau_union_of_mem_primeFactors hG hpE with (h | h) | h
    · exact tau1_subset_sigma_compl M h
    · exact tau2_subset_sigma_compl M h
    · exact tau3_subset_sigma_compl M h
  have hKq' : Subgroup.IsPiSubgroup (({q} : Set ℕ)ᶜ) K := by
    intro p hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hK_le_derivedM),
        Nat.card_pos.ne'⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact tau1_not_mem_derived_primeFactors hqτ1 hpM'
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) ⊓ M :=
    le_inf (hQE.trans (hKdef ▸ Ch04.subgroup_le_normalizer_commutator_self E Q)) hQM
  -- Proposition 10.11(d): `K' := ⁅K, Q⁆ ≤ C_G(M_σ)`, cyclic, `M ≤ N_G(K')`.
  obtain ⟨hK'cent, hK'cyc, hMNK'⟩ :=
    sigma_complement_commutator_cyclic_normal hG hsetup.mem_maximal hKM hKσ' hqτ1.1 hQ hQNK hCQ
      hKab hKq'
  set K' : Subgroup G := ⁅K, Q⁆ with hK'def
  have hK'_le_K : K' ≤ K := hK'def ▸ Ch04.commutator_le_of_le_normalizer (le_inf_iff.mp hQNK).1
  have hK'E : K' ≤ E := hK'_le_K.trans hKE
  -- S5: `K' ≠ ⊥` (else `Q ≤ F(E)`).
  have hK'ne : K' ≠ ⊥ := by
    intro hbot
    apply hQF
    have hQab : IsMulCommutative ↥Q := ⟨⟨hQ.1.comm⟩⟩
    rw [hK'def, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    exact Q_le_fittingInG_of_commutator_centralizesQ hQE hQab (hKdef ▸ hKab) (hKdef ▸ hbot)
  -- Every prime of `K'` lies in `τ₂(M)`.
  have hπτ2 : ∀ p ∈ (Nat.card ↥K').primeFactors, p ∈ tau2 M := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    haveI : Fact p.Prime := ⟨hpp⟩
    by_contra hpτ2
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le hK'E), Nat.card_pos.ne'⟩
    have hpτ : p ∈ tau1 M ∪ tau2 M ∪ tau3 M := hsetup.mem_tau_union_of_mem_primeFactors hG hpE
    have hr1 : pRank ↥M p = 1 := by
      rcases hpτ with (h | h) | h
      · exact h.2.2
      · exact absurd h hpτ2
      · exact h.2.2
    obtain ⟨a, hacard⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') p hpd
    set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
    have hAK' : A ≤ K' := by rw [hAdef, Subgroup.zpowers_le]; exact a.2
    have haGcard : orderOf (a : G) = p :=
      (orderOf_injective K'.subtype K'.subtype_injective a).trans hacard
    have hAcard : Nat.card ↥A = p := by rw [hAdef, Nat.card_zpowers]; exact haGcard
    have hAelem : A.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hAcard
    have hA : A ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      rw [hr1, mem_elemAbelianOfRank]; exact ⟨hAelem, by rw [hAcard, pow_one]⟩
    have hpπ : p ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans (Subgroup.card_dvd_of_le (hK'E.trans hsetup.E_le)),
        Nat.card_pos.ne'⟩
    have hpσ : p ∉ sigma M := by
      rcases hpτ with (h | h) | h
      · exact tau1_subset_sigma_compl M h
      · exact tau2_subset_sigma_compl M h
      · exact tau3_subset_sigma_compl M h
    have hpκ : p ∉ kappa M := by rw [hF]; exact Set.notMem_empty p
    have hAM : A ≤ M := hAK'.trans (hK'E.trans hsetup.E_le)
    obtain ⟨_, hCA, _⟩ := msigma_structure_of_notMem_sigma_kappa hG hsetup.mem_maximal hpπ hpσ hpκ hA hAM
    have hAcent : A ≤ Subgroup.centralizer (Msigma M : Set G) := hAK'.trans hK'cent
    have hMσcentA : Msigma M ≤ Subgroup.centralizer (A : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hAcent
    have hinf : Msigma M ⊓ Subgroup.centralizer (A : Set G) = Msigma M :=
      inf_eq_left.mpr hMσcentA
    rw [hCA] at hinf
    exact Msigma_ne_bot hG hsetup.mem_maximal hinf.symm
  -- `Q` acts fixed-point-freely on `K'`: coprime identity `⁅K', Q⁆ = K'`.
  have hqprime : q.Prime := Fact.out
  haveI hK'ab : IsMulCommutative ↥K' := isMulCommutative_of_le (hKdef ▸ hKab) hK'_le_K
  have hQNK' : Q ≤ Subgroup.normalizer (K' : Set G) := hQM.trans hMNK'
  have hqnK : ¬ q ∣ Nat.card ↥K := fun hdvd =>
    hKq' q (Nat.mem_primeFactors.mpr ⟨hqprime, hdvd, Nat.card_pos.ne'⟩) rfl
  have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
  have hcopKQ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q) := by
    rw [hQcard]; exact (hqprime.coprime_iff_not_dvd.mpr hqnK).symm
  have hqnK' : ¬ q ∣ Nat.card ↥K' := fun hdvd =>
    hqnK (hdvd.trans (Subgroup.card_dvd_of_le hK'_le_K))
  have hcopK'Q : Nat.Coprime (Nat.card ↥K') (Nat.card ↥Q) := by
    rw [hQcard]; exact (hqprime.coprime_iff_not_dvd.mpr hqnK').symm
  have hident : (⁅K', Q⁆ : Subgroup G) = K' := by
    haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hsetup.mem_maximal
    haveI : IsSolvable ↥(K ⊔ Q) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective (sup_le hKM hQM))
    have hid := commutator_commutator_right_eq_of_le_normalizer (D := K) (Q := Q)
      ‹IsSolvable ↥(K ⊔ Q)› (le_inf_iff.mp hQNK).1 hcopKQ
    rw [← hK'def] at hid
    exact hid
  have hFPF : Subgroup.centralizer (Q : Set G) ⊓ K' = ⊥ := by
    obtain ⟨hdisj, -⟩ :=
      OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := K') (K := Q) hQNK' hcopK'Q
    rwa [hident, inf_assoc, inf_idem] at hdisj
  exact ⟨K', hK'E, hK'ne, hK'cyc, hK'cent, hMNK', hπτ2, hFPF⟩

/-- **BG Lemma 14.11, A-choice**: for a normal line `L ◁ M` of order `p` with `p ∈ τ₂(M)` and
`L ≤ E`, there is `A ∈ ℰ_p²(E)` with `L ≤ A`.

`N_G(L) = M` (as `M ≤ N_G(L) < ⊤` and `M` is maximal), so BG Lemma 10.5
(`pRank_eq_two_of_normalizer_le`) yields `A₀ ∈ ℰ_p²(G)` with `L ≤ A₀`; `A₀` is abelian and
contains `L`, so `A₀ ≤ C_G(L) ≤ N_G(L) = M`.  As a `τ₂`-subgroup of `M`, `A₀` conjugates into the
`τ₂`-Hall `E₂ ≤ E` by some `w ∈ M` (`exists_conj_smul_le_hallPiece`); `L` is `M`-invariant so
`L = L^w ≤ A₀^w`, and `A₀^w ∈ ℰ_p²(E)`. -/
theorem exists_elemAb_rank_two_le_E_containing_line [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ L : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hsetup : SubgroupESetup M E E₁ E₂ E₃) (hp : p ∈ tau2 M)
    (hLE : L ≤ E) (hLM_norm : M ≤ Subgroup.normalizer (L : Set G))
    (hL : L ∈ elemAbelianOfRank G p 1) :
    ∃ A ∈ elemAbelianOfRank G p 2, A ≤ E ∧ L ≤ A := by
  classical
  have hLM : L ≤ M := hLE.trans hsetup.E_le
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hL
  have hM_coatom : IsCoatom M := hsetup.mem_maximal
  -- `N_G(L) = M`.
  have hNL_lt : Subgroup.normalizer (L : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hsetup.mem_maximal hLM hLne
  have hNLM : Subgroup.normalizer (L : Set G) ≤ M := by
    rcases eq_or_lt_of_le hLM_norm with heq | hlt
    · exact heq.ge
    · exact absurd (hM_coatom.2 _ hlt) hNL_lt.ne
  -- BG Lemma 10.5: `∃ A₀ ∈ ℰ_p²(G), L ≤ A₀`.
  obtain ⟨-, -, A₀, hA₀, hLA₀⟩ :=
    OddOrder.BG.Ch3.S10.pRank_eq_two_of_normalizer_le hG hsetup.mem_maximal
      (tau2_subset_sigma_compl M hp) hL hNLM
  have hA₀card : Nat.card ↥A₀ = p ^ 2 := hA₀.2
  have hA₀ab : IsMulCommutative ↥A₀ := ⟨⟨hA₀.1.comm⟩⟩
  -- `A₀ ≤ M` (abelian, contains `L`).
  have hA₀M : A₀ ≤ M :=
    (le_centralizer_of_le_of_le hA₀ab le_rfl hLA₀).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNLM)
  -- `A₀` is a `τ₂(M)`-subgroup.
  have hA₀pi : Ch03.Subgroup.IsPiGroup (tau2 M) (A₀.subgroupOf M) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv, hA₀card] at hr
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hr
    rwa [(Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow hr_dvd)]
  -- Conjugate `A₀` into the `τ₂`-Hall `E₂`.
  obtain ⟨w, hwM, hw⟩ :=
    exists_conj_smul_le_hallPiece hG hsetup hsetup.E₂_le hsetup.E₂_hall
      (tau2_subset_sigma_compl M) hA₀M hA₀pi
  refine ⟨MulAut.conj w • A₀, conj_smul_mem_elemAbelianOfRank w hA₀, hw.trans hsetup.E₂_le, ?_⟩
  have hLfix : MulAut.conj w • L = L := conj_smul_eq_self_of_mem_normalizer (hLM_norm hwM)
  calc L = MulAut.conj w • L := hLfix.symm
    _ ≤ MulAut.conj w • A₀ := by
        rw [mulAut_smul_eq_map, mulAut_smul_eq_map]; exact Subgroup.map_mono hLA₀

/-- **BG Lemma 14.11** (mmd L4086): for `M ∈ 𝓜_F` with `E` a complement of `M_σ` in `M`, a
prime `q ∈ π(E)`, and `Q ∈ ℰ_q¹(E)` with `Q ⊄ F(E)`, there is `M* ∈ 𝓜` with either
(1) `q ∈ τ₂(M*)` and `𝓜(C_G(Q)) = {M*}`, or (2) `q ∈ κ(M*)` and `M* ∈ 𝓜_{P₁}`.

"Of independent interest" (BG L4084); used here only by Corollary 14.12.  `F(E)` is the Fitting
subgroup of the complement `E`, taken in `G` via `fittingInG`.

Phase 1 (`q ∈ τ₁(M)`, `C_{M_σ}(Q) = 1`) is `typeF_complement_q_tau1_and_centralizer`.  The
remaining phases — `τ₂(M) ≠ ∅` via the cyclic-normal `⁅E,Q⁆` (Prop 10.11(d) +
`commutator_commutator_right_eq_of_le_normalizer` / a `Q^E`-nilpotent argument for `⁅E,Q⁆ ≠ 1`),
then Cor 12.9 (`commutator_decomp_of_tau1_action`) and the `M*`-dichotomy via Lemma 12.11
(`tau2_transfer_to_maximal`) — are tracked in `issues/7007`. -/
theorem exists_maximal_of_typeF_notMem_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E Q : Subgroup G} {q : ℕ} (hM : M ∈ maximalSubgroups G) (hF : IsTypeF M)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hEM : E ≤ M)
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ Mstar : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      ((q ∈ tau2 Mstar ∧
          maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Mstar}) ∨
       (q ∈ kappa Mstar ∧ IsTypeP1 Mstar)) := by
  classical
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := esetup_of_isComplement hG hM hE hEM
  have hqpf : q ∈ (Nat.card ↥E).primeFactors := hq
  haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqpf⟩
  have hqprime : q.Prime := Fact.out
  obtain ⟨K', hK'E, hK'ne, hK'cyc, hK'cent, hMNK', hπK'τ2, hFPF⟩ :=
    exists_typeF_complement_cyclic_commutator hG hsetup hF hq hQ hQE hQF
  haveI : IsCyclic ↥K' := hK'cyc
  obtain ⟨p, hpp, hpd⟩ :=
    Nat.exists_prime_and_dvd (show Nat.card ↥K' ≠ 1 from fun h => hK'ne (Subgroup.card_eq_one.mp h))
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpτ2 : p ∈ tau2 M := hπK'τ2 p (Nat.mem_primeFactors.mpr ⟨hpp, hpd, Nat.card_pos.ne'⟩)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') p hpd
  set L : Subgroup G := Subgroup.zpowers (a : G) with hLdef
  have haG : orderOf (a : G) = p :=
    (orderOf_injective K'.subtype K'.subtype_injective a).trans ha
  have hLcard : Nat.card ↥L = p := by rw [hLdef, Nat.card_zpowers, haG]
  have hLK' : L ≤ K' := by rw [hLdef, Subgroup.zpowers_le]; exact a.2
  have hLE : L ≤ E := hLK'.trans hK'E
  have hLelem : L ∈ elemAbelianOfRank G p 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hLcard, by rw [hLcard, pow_one]⟩
  have hLne : L ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hLelem
  have hLM_norm : M ≤ Subgroup.normalizer (L : Set G) := by
    haveI : (L.subgroupOf K').Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro m hm
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := K') (C := L.subgroupOf K') (hMNK' hm)
    rwa [Subgroup.map_subgroupOf_eq_of_le hLK'] at hmem
  have hLQ : (⁅L, Q⁆ : Subgroup G) ≠ ⊥ := by
    rw [Ne, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun hLc => hLne (le_bot_iff.mp (hFPF ▸ le_inf hLc hLK'))
  obtain ⟨A, hA, hAE, hLA⟩ :=
    exists_elemAb_rank_two_le_E_containing_line hG hsetup hpτ2 hLE hLM_norm hLelem
  have hAQ : (⁅A, Q⁆ : Subgroup G) ≠ ⊥ := fun h =>
    hLQ (le_bot_iff.mp ((Subgroup.commutator_mono hLA le_rfl).trans h.le))
  have hAne : A ≠ ⊥ := by
    intro h; have h2 := hA.2; rw [h, Subgroup.card_bot] at h2
    exact (Nat.one_lt_pow (by norm_num) hpp.one_lt).ne' h2.symm
  obtain ⟨hqτ1, hCQ⟩ := typeF_complement_q_tau1_and_centralizer hG hsetup hF hq hQ hQE hQF
  obtain ⟨-, -, hA₁elem, -, -⟩ :=
    commutator_decomp_of_tau1_action hG hsetup hpτ2 hqτ1 hA hAE hQ hQE hCQ hAQ
  have hA₁ne : A ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one hA₁elem
  obtain ⟨⟨hENA, -⟩, -, -⟩ := elemAb_normal_in_E_of_tau2 hG hsetup hpτ2 hA hAE
  have hQNA : Q ≤ Subgroup.normalizer (A : Set G) := hQE.trans hENA
  have hQncA : ¬ Q ≤ Subgroup.centralizer (A : Set G) := fun h =>
    hAQ ((Subgroup.commutator_comm A Q).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h))
  have hNA_lt : Subgroup.normalizer (A : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hM (hAE.trans hsetup.E_le) hAne
  obtain ⟨Mstar, hMstar_coatom, hMstar_le⟩ :=
    (eq_top_or_exists_le_coatom _).resolve_left hNA_lt.ne
  have hMstarmax : Mstar ∈ maximalSubgroups G := hMstar_coatom
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstar_coatom, hMstar_le⟩
  have hAMstar : A ≤ Mstar := Subgroup.le_normalizer.trans hMstar_le
  have hQMstar : Q ≤ Mstar := hQNA.trans hMstar_le
  have hqidx : q ∈
      (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors := by
    set c : Subgroup G := E ⊓ Subgroup.centralizer (A : Set G) with hcdef
    have hcE : c ≤ E := inf_le_left
    have hENc : E ≤ Subgroup.normalizer (c : Set G) :=
      hcdef ▸ le_normalizer_inf Subgroup.le_normalizer
        (hENA.trans (normalizer_le_normalizer_centralizer A))
    haveI hcnorm : (c.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hcE).mpr hENc
    have hQ'qg : IsPGroup q ↥(Q.subgroupOf E) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQE).toEquiv, hQ.2]⟩
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
      ⟨hqprime, prime_dvd_index_of_sylow_not_le_of_normal P hPnc, Subgroup.index_ne_zero_of_finite⟩
  obtain ⟨hσβ, hτ12, -⟩ := tau2_transfer_to_maximal hG hsetup hpτ2 hA hAE hMstarmem
  have hpσβ : p ∈ OddOrder.BG.Ch3.S10.sigma Mstar \ OddOrder.BG.Ch3.S10.beta Mstar := hσβ p hpp hpτ2
  have hqτ12 : q ∈ tau1 Mstar ∪ tau2 Mstar := hτ12 q hqidx
  have hApiσ : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma Mstar) A := by
    intro r hr
    rw [hA.2, Nat.mem_primeFactors] at hr
    exact ((Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)) ▸ hpσβ.1
  have hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma Mstar :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall (OddOrder.BG.Ch3.S10.Msigma_isHall hG hMstarmax) hAMstar hApiσ
  have hCMσQ : OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := fun h =>
    hA₁ne (le_bot_iff.mp (h ▸ inf_le_inf hAMσ le_rfl))
  refine ⟨Mstar, hMstarmax, ?_⟩
  rcases hqτ12 with hτ1 | hτ2
  · refine Or.inr ⟨⟨hqprime, Or.inl hτ1, Q, hQ, hQMstar, hCMσQ⟩, ?_⟩
    have hPtype : IsTypeP Mstar := ⟨q, hqprime, Or.inl hτ1, Q, hQ, hQMstar, hCMσQ⟩
    rcases (isTypeP_iff_isTypeP1_or_isTypeP2).mp hPtype with h1 | h2
    · exact h1
    · exfalso
      haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstarmax
      obtain ⟨Ksub, hKsub⟩ := Ch03.hall_E_exists (G := ↥Mstar) (kappa Mstar)
      obtain ⟨Usub, hUsub⟩ :=
        Ch03.hall_E_exists (G := ↥Mstar) ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      have hKeq : (Ksub.map Mstar.subtype).subgroupOf Mstar = Ksub :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Ksub
      have hUeq : (Usub.map Mstar.subtype).subgroupOf Mstar = Usub :=
        Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective Usub
      have hσeqβ :=
        ((typeP_structure hG hMstarmax hPtype (Subgroup.map_subtype_le _)
            (by rw [hKeq]; exact hKsub) rfl (by rw [hUeq]; exact hUsub)).2.2.2.2.1 h2).1
      exact hpσβ.2 (hσeqβ ▸ hpσβ.1)
  · refine Or.inl ⟨hτ2, ?_⟩
    have hQcard : Nat.card ↥Q = q := by rw [hQ.2, pow_one]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) q (hQcard ▸ dvd_refl q)
    have hxG : orderOf (x : G) = q := (orderOf_injective Q.subtype Q.subtype_injective x).trans hx
    set X : G := (x : G) with hXdef
    have hXQ : X ∈ Q := x.2
    have hX1 : X ≠ 1 := by
      intro h; rw [h, orderOf_one] at hxG; exact hqprime.ne_one hxG.symm
    have hcl : Subgroup.closure ({X} : Set G) = Q := by
      rw [← Subgroup.zpowers_eq_closure]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hXQ)
        (le_of_eq (by rw [hQcard, Nat.card_zpowers, hxG]))
    have hCeq : Subgroup.centralizer ({X} : Set G) = Subgroup.centralizer (Q : Set G) := by
      rw [← hcl]; exact (Subgroup.centralizer_closure {X}).symm
    have hτ2cl : ∀ r ∈ piSet (Subgroup.closure ({X} : Set G)), r ∈ tau2 Mstar := by
      intro r hr
      rw [hcl, piSet, Set.mem_setOf_eq, hQcard, Nat.mem_primeFactors] at hr
      exact ((Nat.prime_dvd_prime_iff_eq hr.1 hqprime).mp hr.2.1) ▸ hτ2
    have hsingle := maximalContaining_centralizer_eq_singleton_of_tau2_element hG hMstarmax
      (hQMstar hXQ) hX1 hτ2cl (by rw [hCeq]; exact hCMσQ)
    rwa [hCeq] at hsingle

/-- **BG Theorem A(5), element form** (mmd L4280): for a type-`P` maximal subgroup `M` with cyclic
Hall `κ(M)`-subgroup `K` and `K* = C_{M_σ}(K)`, the `M`-centralizer of every nonidentity `k ∈ K`
is the cyclic product `K ⊔ K*` (BG's `C_M(k) = K × K*`).

This sharpens Proposition 14.2(b1) (`typeP_structure`), which gives `N_M(X) = K ⊔ K*` only for the
rank-one `X ∈ ℰ¹(K)`, to the element-wise centralizer.  Bridge: `K` is cyclic, so `⟨k⟩ ≤ K` is
cyclic and contains a subgroup `X` of prime order `p ∣ |k|` with `X ≤ K`; then
`C_G(k) ≤ C_G(X) ≤ N_G(X)`, so `M ⊓ C_G(k) ≤ N_G(X) ⊓ M = K ⊔ K*`, while `K ≤ C_G(k)` (`K` abelian)
and `K* ≤ C_G(K) ≤ C_G(k)` give the reverse. -/
theorem typeP_centralizer_kappaElement_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] :
    ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar := by
  intro k hk hk1
  -- `⟨k⟩ ≤ K`.
  have hzk : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
  -- A prime `p ∣ |k|` and an element `v ∈ ⟨k⟩` of order `p`.
  have hord1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpk⟩ := (orderOf k).exists_prime_and_dvd hord1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpcard : p ∣ Nat.card ↥(Subgroup.zpowers k) := by rw [Nat.card_zpowers]; exact hpk
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hpcard
  -- `X = ⟨v⟩` is rank-one elementary abelian and `X ≤ K`.
  set X : Subgroup G := Subgroup.zpowers (v : G) with hXdef
  have hXcard : Nat.card ↥X = p := by
    rw [hXdef, Nat.card_zpowers]
    exact (orderOf_injective _ (Subgroup.zpowers k).subtype_injective v).trans hv
  have hXelem : X ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXzk : X ≤ Subgroup.zpowers k := by rw [hXdef]; exact Subgroup.zpowers_le.mpr v.2
  have hXK : X ≤ K := hXzk.trans hzk
  -- Proposition 14.2(b1): `N_G(X) ⊓ M = K ⊔ K*`.
  obtain ⟨_, _, hb1, _, _, _, _⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  have hNX : Subgroup.normalizer (X : Set G) ⊓ M = K ⊔ Kstar := hb1 p hp X hXelem hXK
  -- `C_G(k) ≤ C_G(X)`: everything centralizing `k` centralizes `⟨k⟩ ⊇ X`.
  have hCkX : Subgroup.centralizer ({k} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hkCg : k ∈ Subgroup.centralizer ({g} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
    have hyCg : y ∈ Subgroup.centralizer ({g} : Set G) :=
      (Subgroup.zpowers_le.mpr hkCg) (hXzk hy)
    exact Subgroup.mem_centralizer_singleton_iff.mp hyCg
  -- Forward `M ⊓ C_G(k) ≤ K ⊔ K*` via `C_G(k) ≤ C_G(X) ≤ N_G(X)`.
  have hfwd : M ⊓ Subgroup.centralizer ({k} : Set G) ≤ K ⊔ Kstar := by
    rw [← hNX]
    exact le_inf
      (inf_le_right.trans (hCkX.trans (Subgroup.centralizer_le_normalizer (X : Set G)))) inf_le_left
  -- Reverse `K ⊔ K* ≤ M ⊓ C_G(k)`.
  have hrev : K ⊔ Kstar ≤ M ⊓ Subgroup.centralizer ({k} : Set G) := by
    refine sup_le (le_inf hKM ?_) ?_
    · -- `K ≤ C_G(k)`: `K` cyclic ⟹ `K ≤ C_G(K) ≤ C_G(k)` (`k ∈ K`).
      exact le_trans (Subgroup.le_centralizer K)
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk))
    · -- `K* ≤ M_σ ≤ M` and `K* ≤ C_G(K) ≤ C_G(k)`.
      rw [hKstar]
      exact le_inf (inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M))
        (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk)))
  exact le_antisymm hfwd hrev

/-- **σ-part of a κ-branch element lies in `K*`** (the `Ks_y` step of κ→Ẑ): for a type-`P`
maximal `M`, a `σ(M)`-element `y` that centralizes a nonidentity `κ`-Hall element `y' ∈ K^#` lies
in `K* = M_σ ⊓ C_G(K)`.  Chain: `y ∈ M ⊓ C_G(y') = K ⊔ K*` (`typeP_centralizer_kappaElement_eq`,
conjunct (d)); since `K ⊔ K*` is cyclic (`typeP_Z_isCyclic`), `y` centralizes `K`
(`mem_centralizer_of_mem_sup_isCyclic`); with `y ∈ M_σ` this gives `y ∈ K*`. -/
theorem typeP_sigmaElement_mem_Kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy'K : y' ∈ K) (hy'1 : y' ≠ 1)
    (hcent : y ∈ Subgroup.centralizer ({y'} : Set G)) :
    y ∈ Kstar := by
  haveI hcycZ : IsCyclic ↥(K ⊔ Kstar) :=
    typeP_Z_isCyclic hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
  haveI hcycK : IsCyclic ↥K :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  have hyM : y ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hyMsigma
  have hyMC : y ∈ M ⊓ Subgroup.centralizer ({y'} : Set G) := Subgroup.mem_inf.mpr ⟨hyM, hcent⟩
  rw [typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU y' hy'K hy'1] at hyMC
  rw [hKstar]
  exact Subgroup.mem_inf.mpr ⟨hyMsigma, mem_centralizer_of_mem_sup_isCyclic hcycZ hyMC⟩

/-- **κ→Ẑ membership, core** (the `y'∈K` form): for a type-`P` maximal `M`, a nonidentity
`σ(M)`-element `y` and a nonidentity `κ`-Hall element `y' ∈ K^#` that commute have product
`y · y' ∈ Ẑ = (K ⊔ K*) ∖ (K ∪ K*)`.  Combines `typeP_sigmaElement_mem_Kstar` (`y ∈ K*`) with
`mem_zTilde_of_mul` (using `K ⊓ K* = ⊥`, `kappaHall_inf_Kstar_eq_bot`).  The general κ-branch
element (Coq `mFT_partition` part 2) reduces to this by conjugating its `κ`-element into `K`. -/
theorem kappa_branch_mem_zTilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : IsTypeP M) (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy1 : y ≠ 1) (hy'K : y' ∈ K)
    (hy'1 : y' ≠ 1) (hcent : y ∈ Subgroup.centralizer ({y'} : Set G)) :
    y * y' ∈ zTilde K Kstar :=
  mem_zTilde_of_mul (kappaHall_inf_Kstar_eq_bot hKM hK hKstar)
    (typeP_sigmaElement_mem_Kstar hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hyMsigma hy'K hy'1 hcent)
    hy1 hy'K hy'1

/-- **κ→Ẑ membership, general form**: lifts `kappa_branch_mem_zTilde` to a `κ(M)`-element `y'` not
necessarily in the chosen Hall `K`, via conjugation.  Since `⟨y'⟩` is a `κ(M)`-subgroup of `M`, an
`a ∈ M` conjugates it into `K` (`exists_conj_smul_le_of_isHall`); then `aᵃ • (y · y')` lies in `Ẑ`
(applying the core to `aᵃ • y ∈ M_σ` and `aᵃ • y' ∈ K`), so `y · y' ∈ 𝒞_G(Ẑ)`.  This is the
κ-branch → `𝒞_G(Ẑ)` step of the NonType-I `G^#` cover (Coq `mFT_partition` part 2). -/
theorem kappa_branch_mem_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {M K Kstar U Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hMstarmem : IsZFamilyMember M K Mstar) (hMstarne : Mstar ≠ M)
    (hpart : ∀ N : Subgroup G, IsZFamilyMember M K N → N = M ∨ N = Mstar)
    {y y' : G} (hyMsigma : y ∈ OddOrder.BG.Ch3.S10.Msigma M) (hy1 : y ≠ 1) (hy'M : y' ∈ M)
    (hy'1 : y' ≠ 1) (hcent : y ∈ Subgroup.centralizer ({y'} : Set G))
    (hy'kappa : OddOrder.GroupTheory.IsPiElement (kappa M) y') :
    y * y' ∈ conjClassSet (zTilde K Kstar) := by
  classical
  -- `⟨y'⟩` is a `κ(M)`-subgroup of `M`; conjugate it into `K`.
  have hcloseM : Subgroup.closure ({y'} : Set G) ≤ M := by
    rw [Subgroup.closure_le]; exact Set.singleton_subset_iff.mpr hy'M
  have hcard : Nat.card ↥((Subgroup.closure ({y'} : Set G)).subgroupOf M) = orderOf y' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcloseM).toEquiv,
      ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hclosepi : Ch03.Subgroup.IsPiGroup (kappa M)
      ((Subgroup.closure ({y'} : Set G)).subgroupOf M) := fun p hp =>
    hy'kappa p (by rwa [hcard] at hp)
  obtain ⟨a, haM, hale⟩ := exists_conj_smul_le_of_isHall hG hM hKM hK hcloseM hclosepi
  have hay'K : MulAut.conj a • y' ∈ K :=
    hale (Subgroup.smul_mem_pointwise_smul y' (MulAut.conj a) _
      (Subgroup.subset_closure (Set.mem_singleton y')))
  -- `aᵃ • y ∈ M_σ`.
  have hMsigmaFix : MulAut.conj a • OddOrder.BG.Ch3.S10.Msigma M = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [← Msigma_conj_smul, Subgroup.conj_smul_eq_self_of_mem haM]
  have hayMsigma : MulAut.conj a • y ∈ OddOrder.BG.Ch3.S10.Msigma M :=
    hMsigmaFix ▸ Subgroup.smul_mem_pointwise_smul y (MulAut.conj a) _ hyMsigma
  have hay1 : MulAut.conj a • y ≠ 1 := fun h => hy1 (by
    rw [MulAut.smul_def] at h; exact (MulAut.conj a).injective (h.trans (map_one _).symm))
  have hay'1 : MulAut.conj a • y' ≠ 1 := fun h => hy'1 (by
    rw [MulAut.smul_def] at h; exact (MulAut.conj a).injective (h.trans (map_one _).symm))
  -- `aᵃ • y` centralizes `aᵃ • y'`.
  have haycent : MulAut.conj a • y ∈ Subgroup.centralizer ({MulAut.conj a • y'} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz, MulAut.smul_def, MulAut.smul_def, ← map_mul, ← map_mul]
    exact congrArg (MulAut.conj a) (Subgroup.mem_centralizer_iff.mp hcent y' (Set.mem_singleton y'))
  -- `aᵃ • (y·y') = (aᵃ • y)·(aᵃ • y') ∈ Ẑ`, so `y·y' ∈ 𝒞_G(Ẑ)`.
  have hzin : MulAut.conj a • (y * y') ∈ zTilde K Kstar := by
    rw [MulAut.smul_def, map_mul, ← MulAut.smul_def, ← MulAut.smul_def]
    exact kappa_branch_mem_zTilde hG D hM hP hKM hK hKstar hU hMstarmem hMstarne hpart
      hayMsigma hay1 hay'K hay'1 haycent
  exact ⟨MulAut.conj a • (y * y'), hzin, a⁻¹, by
    rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

/-- **κ-branch of the dichotomy → `𝒞_G(Ẑ)`**: the κ branch of `sigma_decomposition_dichotomy`
(`y` with `ℓ_σ(y)=1`, a maximal `N ∈ 𝓜_σ(y)`, `y⁻¹g ∈ (C_N[y])^#` a `κ(N)`-element) places `g`
in `𝒞_G(Ẑ)` for the type-`P` neighbour `N`'s exceptional subgroup `Ẑ`.  `N` is type-`P` (it has a
`κ`-element), so `exists_typeP_data`/`exists_partner` supply its Theorem 14.7 data, and
`kappa_branch_mem_conjClassSet_zTilde` finishes (`y · (y⁻¹g) = g`).  This is the κ branch of the
NonType-I `G^#` cover (Coq `mFT_partition` part 2). -/
theorem kappa_branch_dichotomy_mem_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {y g : G}
    (hyl : D.length y = 1) {N : Subgroup G}
    (hNmem : N ∈ maximalSigmaSubgroupsOfElement y)
    (hsharp : y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)))
    (hkappa : OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) :
    ∃ K Kstar : Subgroup G, g ∈ conjClassSet (zTilde K Kstar) := by
  obtain ⟨hNmax, hyNsigma⟩ := hNmem
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hyl).1
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_inf] at hsharp
  obtain ⟨⟨hy'N, hy'cent⟩, hy'1⟩ := hsharp
  have hycent : y ∈ Subgroup.centralizer ({y⁻¹ * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hy'cent y (Set.mem_singleton y)).symm
  have hNP : IsTypeP N := by
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    exact ⟨p, hkappa p hp⟩
  obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hNmax
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hNmax hNP hKM hK hKstar hU
  refine ⟨K, Kstar, ?_⟩
  have hmem := kappa_branch_mem_conjClassSet_zTilde hG D hNmax hNP hKM hK hKstar hU hMstarmem
    hMstarne hpart hyNsigma hy1 hy'N hy'1 hycent hkappa
  rwa [mul_inv_cancel_left] at hmem

/-- **Fixed-`W` κ-branch**: the same conclusion as `kappa_branch_dichotomy_mem_conjClassSet_zTilde`,
but landing in the `Ẑ` of a *fixed* reference type-`P` maximal `Mref` (data `Kref, K*ref, Uref`)
rather than in the (existentially produced) type-`P` `N`'s own `Ẑ`.  The dichotomy's `N` is type-`P`,
so `conjClassSet_zTilde_eq_fixed_of_isTypeP` (fix-`W`) absorbs `N`'s `Ẑ` into `Ẑ(Mref)`. -/
theorem kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {y g : G} (hyl : D.length y = 1) {N : Subgroup G}
    (hNmem : N ∈ maximalSigmaSubgroupsOfElement y)
    (hsharp : y⁻¹ * g ∈ sharpSubgroup (N ⊓ Subgroup.centralizer ({y} : Set G)))
    (hkappa : OddOrder.GroupTheory.IsPiElement (kappa N) (y⁻¹ * g)) :
    g ∈ conjClassSet (zTilde Kref Kstarref) := by
  obtain ⟨hNmax, hyNsigma⟩ := hNmem
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hyl).1
  rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.mem_inf] at hsharp
  obtain ⟨⟨hy'N, hy'cent⟩, hy'1⟩ := hsharp
  have hycent : y ∈ Subgroup.centralizer ({y⁻¹ * g} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]; intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (Subgroup.mem_centralizer_iff.mp hy'cent y (Set.mem_singleton y)).symm
  have hNP : IsTypeP N := by
    obtain ⟨p, hp⟩ : (orderOf (y⁻¹ * g)).primeFactors.Nonempty :=
      Nat.nonempty_primeFactors.mpr (by
        have h1 : orderOf (y⁻¹ * g) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
        have h0 : 0 < orderOf (y⁻¹ * g) := orderOf_pos _
        omega)
    exact ⟨p, hkappa p hp⟩
  obtain ⟨K, Kstar, U, hKM, hK, hKstar, hU⟩ := exists_typeP_data hG hNmax
  obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ := exists_partner hG D hNmax hNP hKM hK hKstar hU
  have hmem : g ∈ conjClassSet (zTilde K Kstar) := by
    have h := kappa_branch_mem_conjClassSet_zTilde hG D hNmax hNP hKM hK hKstar hU hMstarmem
      hMstarne hpart hyNsigma hy1 hy'N hy'1 hycent hkappa
    rwa [mul_inv_cancel_left] at h
  rwa [conjClassSet_zTilde_eq_fixed_of_isTypeP hG hMref hMPref hKMref hKref hKstarref hUref
    hNmax hNP hKM hK hKstar] at hmem

/-- **`G^#` cover dichotomy** (the `⊆` of BG Corollary 14.9's `G^#` partition, both cases): every
`g ≠ 1` lies in `𝒞_G(M̃)` for some maximal `M`, *or* in `𝒞_G(Ẑ)` for some exceptional pair `(K, K*)`.
Immediate from `sigma_decomposition_dichotomy`: the signalizer branch gives `g ∈ M̃`
(`mem_Mtilde_of_mem_coset`), the κ branch gives `g ∈ 𝒞_G(Ẑ)`
(`kappa_branch_dichotomy_mem_conjClassSet_zTilde`).  Unlike `exists_mem_conjClassSet_Mtilde_of_ne_one`
this needs no all-type-`F` hypothesis — it covers the κ branch with the `Ẑ` piece. -/
theorem exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {g : G} (hg : g ≠ 1) :
    (∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M))
    ∨ (∃ K Kstar : Subgroup G, g ∈ conjClassSet (zTilde K Kstar)) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact Or.inl ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · exact Or.inr (kappa_branch_dichotomy_mem_conjClassSet_zTilde hG D hyl hNmem hsharp hκ)

/-- **Fixed-`W` `G^#` cover** (the form BG Corollary 14.9 / the NonTypeICovering struct needs):
every `g ≠ 1` lies in `𝒞_G(M̃)` for some maximal `M`, or in `𝒞_G(Ẑ)` for the *fixed* exceptional
`Ẑ = zTilde Kref K*ref` of a reference type-`P` maximal `Mref`.  Same as
`exists_mem_conjClassSet_Mtilde_or_zTilde_of_ne_one`, but the κ branch is collapsed onto the single
fixed `Ẑ` via `kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde`. -/
theorem exists_mem_conjClassSet_Mtilde_or_fixed_zTilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Mref Kref Kstarref Uref : Subgroup G}
    (hMref : Mref ∈ maximalSubgroups G) (hMPref : IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (kappa Mref) (Kref.subgroupOf Mref))
    (hKstarref : Kstarref = OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup ((kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref))
    {g : G} (hg : g ≠ 1) :
    (∃ M ∈ maximalSubgroups G,
      g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M))
    ∨ g ∈ conjClassSet (zTilde Kref Kstarref) := by
  set D := genuineSigmaDecomposition hG with hD
  rcases sigma_decomposition_dichotomy hG D hg with
    ⟨y, hyl, hyr⟩ | ⟨y, hyl, N, hNmem, hsharp, hκ⟩
  · obtain ⟨hy1, M, hMmax, hyMσ⟩ := (D.length_one_iff y).mp hyl
    exact Or.inl ⟨M, hMmax, subset_conjClassSet
      (mem_Mtilde_of_mem_coset hG D (Set.mem_sdiff_singleton.mpr ⟨hyMσ, hy1⟩) hyr)⟩
  · exact Or.inr (kappa_branch_dichotomy_mem_fixed_conjClassSet_zTilde hG D hMref hMPref hKMref
      hKref hKstarref hUref hyl hNmem hsharp hκ)

/-- **BG Theorem A(4)** (mmd L4279): `C_U(k) = 1` for `k ∈ K#` — the `(κ(M) ∪ σ(M))'`-Hall
complement `U` meets each `M`-centralizer `C_M(k) = K ⊔ K*` trivially.

**Faithfulness (issue 8017).** BG states A(4) for the *`K`-invariant* complement `U`, but the
conclusion holds for **every** `(κ ∪ σ)'`-Hall `U ≤ M`: by `typeP_centralizer_kappaElement_eq`,
`U ⊓ C_G(k) = U ⊓ (M ⊓ C_G(k)) = U ⊓ (K ⊔ K*)`, and `|U|` (a `(κ ∪ σ)'`-number) is coprime to
`|K ⊔ K*| = |K|·|K*|` (a `(κ ∪ σ)`-number, `K` Hall `κ`, `K* ≤ M_σ` Hall `σ`), so the intersection
is trivial.  No `K`-invariance of `U` is needed; the bug-suspect conjunct is faithful as stated. -/
theorem typeP_hall_inf_centralizer_kappaElement_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] :
    ∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ := by
  intro k hk hk1
  -- `C_M(k) = K ⊔ K*`, hence `U ⊓ C_G(k) = U ⊓ (K ⊔ K*)` (`U ≤ M`).
  have hCM := typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU k hk hk1
  have hstep : U ⊓ Subgroup.centralizer ({k} : Set G) = U ⊓ (K ⊔ Kstar) := by
    rw [← hCM, ← inf_assoc, inf_eq_left.mpr hUM]
  rw [hstep]
  -- `|U|` and `|K ⊔ K*| = |K|·|K*|` are coprime: `(κ∪σ)'` vs `κ∪σ`.
  apply Subgroup.inf_eq_bot_of_coprime
  have hcard : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar :=
    card_kappaHall_sup_Kstar hKM hK hKstar
  refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    (π := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
  · -- `|U|` is a `(κ∪σ)'`-number.
    intro p hp
    exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  · -- every prime of `|K ⊔ K*|` lies in `κ ∪ σ`.
    intro p hp hpcompl
    rw [hcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hp
    rcases Finset.mem_union.mp hp with hpK | hpKstar
    · exact hpcompl (Or.inl (hK.1 p (by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv])))
    · refine hpcompl (Or.inr (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p ?_))
      have hKstar_le_Mσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKstar_le_Mσ) Nat.card_pos.ne' hpKstar

/-- **`M_σ ∩ M* = K*`** (BG Theorem 14.7(d) kernel, Coq `defMsMstar`): for a type-`P₂` maximal
`M` with `κ`-Hall `K`, `K* = M_σ ⊓ C(K)`, and the dual partner `M*` (`K ≤ M*_σ`, `K* ≤ M*`, `M`
not conjugate to `M*`), the intersection `M_σ ⊓ M*` equals `K*`.

`⊇` is immediate (`K* ≤ M_σ`, `K* ≤ M*`).  For `⊆`: any `y ∈ M_σ ⊓ M*` has `⁅⟨y⟩, K⁆ ≤ M_σ`
(`K ≤ M ≤ N(M_σ)`, `y ∈ M_σ`) and `⁅⟨y⟩, K⁆ ≤ M*_σ` (`K ≤ M*_σ ◁ M*`, `y ∈ M* ≤ N(M*_σ)`), so
`⁅⟨y⟩, K⁆ ≤ M_σ ⊓ M*_σ = ⊥` (Lemma 10.12, `M_σ` nilpotent for type-`P₂`); hence `y` centralizes
`K`, i.e. `y ∈ M_σ ⊓ C(K) = K*`.  Avoids the embedding's σ(M)-Hall-of-M* clause. -/
private theorem msigma_inf_partner_eq_kstar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) (hKM : K ≤ M)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hMstarmax : Mstar ∈ maximalSubgroups G)
    (hKMsigmaMstar : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar) (hKstarMstar : Kstar ≤ Mstar)
    (hnc : ¬ IsConjugateSubgroup M Mstar) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar := by
  classical
  -- `M_σ` nilpotent (type-`P₂`) ⟹ `M_σ ⊓ M*_σ = ⊥` (Lemma 10.12).
  have hdisj : OddOrder.BG.Ch3.S10.Msigma M ⊓ OddOrder.BG.Ch3.S10.Msigma Mstar = ⊥ :=
    ((OddOrder.BG.Ch3.S10.disjoint_of_not_conj hG hM hMstarmax (fun h => hnc h)).2
      (msigma_isNilpotent_of_isTypeP2 hG hM hP2)).1
  have hMN : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMstarN : Mstar ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma Mstar : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma Mstar) Mstar
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyMσ, hyMstar⟩ := hy
    rw [hKstar, Subgroup.mem_inf]
    refine ⟨hyMσ, ?_⟩
    have hcle : (⁅Subgroup.zpowers y, K⁆ : Subgroup G) ≤ ⊥ := by
      rw [← hdisj, le_inf_iff]
      refine ⟨Subgroup.commutator_le.mpr ?_, Subgroup.commutator_le.mpr ?_⟩
      · intro a ha k hk
        have haMσ : a ∈ OddOrder.BG.Ch3.S10.Msigma M := (Subgroup.zpowers_le.mpr hyMσ) ha
        have hkN := (Subgroup.mem_normalizer_iff.mp (hMN (hKM hk))) a⁻¹
        rw [commutatorElement_def]
        have hconj : k * a⁻¹ * k⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma M := hkN.mp (inv_mem haMσ)
        have : a * k * a⁻¹ * k⁻¹ = a * (k * a⁻¹ * k⁻¹) := by group
        rw [this]; exact mul_mem haMσ hconj
      · intro a ha k hk
        have haMstarσ : a ∈ Mstar := (Subgroup.zpowers_le.mpr hyMstar) ha
        have hkMσstar : k ∈ OddOrder.BG.Ch3.S10.Msigma Mstar := hKMsigmaMstar hk
        rw [commutatorElement_def]
        have hconj : a * k * a⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma Mstar :=
          (Subgroup.mem_normalizer_iff.mp (hMstarN haMstarσ) k).mp hkMσstar
        have : a * k * a⁻¹ * k⁻¹ = (a * k * a⁻¹) * k⁻¹ := by group
        rw [this]; exact mul_mem hconj (inv_mem hkMσstar)
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcle
    exact hcle (Subgroup.mem_zpowers y)
  · exact le_inf (hKstar ▸ inf_le_left) hKstarMstar

/-- **The partner intersection `ziMMst` and `K`-uniqueness `sK_uniqMst`** (BG Theorem 14.7,
embedding internals), assembled here for the type-`F` classification of Corollary 14.12.

Applying `typeP_structure` to the partner `M*` (whose `κ`-Hall is `K*`, with `K = M*_σ ⊓ C(K*)`):
the `b1` clause at a characteristic order-`p` line of the cyclic `K*` gives `N_{M*}(K*) = K* ⊔ K`,
whence (via `M_σ ⊓ M* = K*`, here `hMsMst`) `M ⊓ M* = K ⊔ K*`; and the `K`-TI clause gives
`K ≤ M*^a ⟹ a ∈ M*`.  Mirrors Coq `Ptype_embedding`'s `ziMMst`/`sK_uniqMst` (BGsection14.v L1820,
L2278). -/
private theorem partner_inf_and_uniq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar Mstar : Subgroup G} (hMstmax : Mstar ∈ maximalSubgroups G) (hMstP : IsTypeP Mstar)
    (hKstarMst : Kstar ≤ Mstar)
    (hKstar_hall : Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar))
    (hK_eq : K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer (Kstar : Set G))
    (hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar)
    (hKM : K ≤ M) (hKstarM : Kstar ≤ M)
    (hZcyc : IsCyclic ↥(K ⊔ Kstar)) (hKstarNe : Kstar ≠ ⊥) (hKNe : K ≠ ⊥)
    (hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mstar = Kstar) :
    M ⊓ Mstar = K ⊔ Kstar ∧ (∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) := by
  classical
  haveI : IsSolvable ↥Mstar := hG.solvable_of_mem_maximalSubgroups hMstmax
  haveI := hZcyc
  -- A Hall `(κ(M*) ∪ σ(M*))'`-subgroup of `M*`, to feed `typeP_structure`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hU_Mstar : Ch03.IsHallSubgroup ((kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  have hstruct := typeP_structure hG hMstmax hMstP hKstarMst hKstar_hall hK_eq hU_Mstar
  -- `b1`: `N_G(X) ⊓ M* = K* ⊔ K` for rank-one `X ≤ K*`; TI: `g ∉ M* → K ⊓ M*^g = ⊥`.
  have hb1 := hstruct.2.2.1
  have hTI := hstruct.2.2.2.1
  -- `K ≤ C(K*)` (`Z = K ⊔ K*` cyclic ⟹ abelian).
  have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
    letI : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hkZ : k ∈ (K ⊔ Kstar : Subgroup G) := Subgroup.mem_sup_left hk
    have hsZ : s ∈ (K ⊔ Kstar : Subgroup G) := Subgroup.mem_sup_right hs
    exact congrArg Subtype.val (mul_comm (⟨s, hsZ⟩ : ↥(K ⊔ Kstar)) (⟨k, hkZ⟩ : ↥(K ⊔ Kstar)))
  -- A characteristic order-`p` line `X ≤ K*` (cyclic `K*`).
  haveI hKstarcyc : IsCyclic ↥Kstar :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_right : Kstar ≤ K ⊔ Kstar)).isCyclic.mp inferInstance
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥Kstar ≠ 1 from fun h => hKstarNe (Subgroup.card_eq_one.mp h))
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Kstar) p hpd
  set X : Subgroup G := Subgroup.zpowers (x : G) with hXdef
  have hxord : orderOf (x : G) = p :=
    (orderOf_injective Kstar.subtype Kstar.subtype_injective x).trans hx
  have hXcard : Nat.card ↥X = p := by rw [hXdef, Nat.card_zpowers, hxord]
  have hXKstar : X ≤ Kstar := by rw [hXdef, Subgroup.zpowers_le]; exact x.2
  have hXelem : X ∈ elemAbelianOfRank G p 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hNKstarX : Subgroup.normalizer (Kstar : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    haveI : (X.subgroupOf Kstar).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro g hg
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := Kstar) (C := X.subgroupOf Kstar) hg
    rwa [Subgroup.map_subgroupOf_eq_of_le hXKstar] at hmem
  -- `N_{M*}(K*) = K* ⊔ K = K ⊔ K*`.
  have hNMst : Subgroup.normalizer (Kstar : Set G) ⊓ Mstar = K ⊔ Kstar := by
    refine le_antisymm ?_ ?_
    · calc Subgroup.normalizer (Kstar : Set G) ⊓ Mstar
          ≤ Subgroup.normalizer (X : Set G) ⊓ Mstar := inf_le_inf hNKstarX le_rfl
        _ = Kstar ⊔ K := hb1 p hp X hXelem hXKstar
        _ = K ⊔ Kstar := sup_comm _ _
    · refine le_inf (sup_le (hKcKstar.trans (Subgroup.centralizer_le_normalizer (Kstar : Set G)))
        Subgroup.le_normalizer) ?_
      exact sup_le (hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)) hKstarMst
  -- `ziMMst`: `M ⊓ M* = K ⊔ K*`.
  have hMN : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hziMMst : M ⊓ Mstar = K ⊔ Kstar := by
    refine le_antisymm ?_ (le_inf (sup_le hKM hKstarM)
      (sup_le (hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mstar)) hKstarMst))
    have hsub : M ⊓ Mstar ≤ Subgroup.normalizer (Kstar : Set G) := by
      rw [← hMsMst]
      exact le_normalizer_inf (inf_le_left.trans hMN) (inf_le_right.trans Subgroup.le_normalizer)
    calc M ⊓ Mstar ≤ Subgroup.normalizer (Kstar : Set G) ⊓ Mstar := le_inf hsub inf_le_right
      _ = K ⊔ Kstar := hNMst
  -- `sK_uniqMst`: `K ≤ M*^a ⟹ a ∈ M*`.
  refine ⟨hziMMst, fun a hKa => ?_⟩
  by_contra haMst
  exact hKNe (le_bot_iff.mp ((hTI a haMst) ▸ le_inf le_rfl hKa))

/-- **BG `defUK`** (Coq `P2type_signalizer`, BGsection14.v L2329): for a type-`P₂` maximal
subgroup `M` with cyclic Hall `κ(M)`-subgroup `K` and abelian `(κ(M) ∪ σ(M))'`-Hall complement
`U` normalized by `K`, the commutator `⁅U, K⁆` equals `U`.

The coprime decomposition `U = (C(K) ⊓ U) ⊔ ⁅U, K⁆` (`fitting_coprime_abelian_decomp`: `U`
abelian, `K ≤ N(U)`, `gcd(|U|,|K|) = 1`) collapses because `C_U(K) = C(K) ⊓ U = ⊥`.  Indeed
Theorem A(4) (`typeP_hall_inf_centralizer_kappaElement_eq_bot`) gives `U ⊓ C(k) = ⊥` for every
`k ∈ K#`, and `C(K) ⊓ U ≤ C(k) ⊓ U` for any such `k` (one exists since `K ≠ ⊥`).  `K` is cyclic
of prime order `q = |K|` by Proposition 14.2(g) (type-`P₂`). -/
theorem typeP2_kappaHall_commutator_eq_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hKNU : K ≤ Subgroup.normalizer (U : Set G)) :
    (⁅U, K⁆ : Subgroup G) = U := by
  classical
  have hP : IsTypeP M := hP2.1
  -- `|K| = q` is prime (Prop 14.2(g) for type-`P₂`), so `K` is cyclic.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstar hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨k₀, hk₀K, hk₀ne⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hKne
  -- `C(K) ⊓ U = ⊥` from Theorem A(4) at `k₀ ∈ K#` (`C(K) ⊓ U ≤ C(k₀) ⊓ U = U ⊓ C(k₀) = ⊥`).
  have hCUK_bot : Subgroup.centralizer (K : Set G) ⊓ U = ⊥ := by
    have hA4 := typeP_hall_inf_centralizer_kappaElement_eq_bot hG hM hP hKM hUM hK hKstar hU
      k₀ hk₀K hk₀ne
    rw [eq_bot_iff, ← hA4]
    exact le_inf inf_le_right
      (inf_le_left.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hk₀K)))
  -- Coprime `|U|` (a `(κ∪σ)'`-number) and `|K|` (a `κ ⊆ κ∪σ` number).
  have hcopUK : Nat.Coprime (Nat.card ↥U) (Nat.card ↥K) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne'
      (fun p _ => hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]))
      (fun p _ hpc => hpc (Or.inl (hK.1 p
        (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]))))
  -- Collapse the coprime decomposition `U = (C(K) ⊓ U) ⊔ ⁅U, K⁆`.
  haveI hUcomm_inst : IsMulCommutative ↥U :=
    ⟨⟨fun a b => Subtype.ext (hUab (a : G) a.2 (b : G) b.2)⟩⟩
  have hd := (OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := U) (K := K) hKNU hcopUK).2
  rwa [hCUK_bot, bot_sup_eq] at hd


/-- **Type-`P₂` is conjugation-invariant**. -/
theorem isTypeP2_conj_smul [Finite G] (g : G) (M : Subgroup G) :
    IsTypeP2 (MulAut.conj g • M) ↔ IsTypeP2 M := by
  unfold IsTypeP2
  rw [kappa_conj_smul, sigmaComplementPrimes_conj_smul, isTypeP_conj_smul]

/-- In a finite nilpotent subgroup `N`, a subgroup `P ≤ N` that is self-normalizing in `N`
(`N_G(P) ⊓ N ≤ P`) must be all of `N` — the normalizer condition: proper subgroups of a
nilpotent group grow under normalization.  Generalizes `sylow_coe_eq_of_normalizer_inf_le`
(`P` need not be Sylow, only `N` nilpotent). -/
private theorem eq_of_isNilpotent_normalizer_inf_le [Finite G] {N P : Subgroup G}
    (hN : Group.IsNilpotent ↥N) (hPN : P ≤ N)
    (hle : Subgroup.normalizer (P : Set G) ⊓ N ≤ P) : N = P := by
  haveI : Group.IsNilpotent ↥N := hN
  have hnc : NormalizerCondition ↥N := Group.normalizerCondition_of_isNilpotent
  have hself : Subgroup.normalizer (P.subgroupOf N) = P.subgroupOf N := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPN]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_) <;>
      rw [Subgroup.mem_subgroupOf] at hx ⊢
    · exact hle ⟨hx, x.2⟩
    · exact P.le_normalizer hx
  have htop : P.subgroupOf N = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hPN

/-- **BG Corollary 14.12** (mmd L4035): for `M ∈ 𝓜_{P₂}` with `K`, `M*`, `K*` as in
Theorem 14.7 and `U` as in Proposition 14.2(a), `r ∈ π(U)`, `R` the Sylow `r`-subgroup of the
abelian `U`, and `H ∈ 𝓜(N_G(R))`: then `H ∈ 𝓜_F`, `U ⊆ H_σ`, `M ∩ H = U K`, `N_H(U) ⊄ M`,
`K ⊆ F(H ∩ M*)`, and `H ∩ M*` complements `H_σ` in `H`.

**Faithfulness (2026-06-22):** the hypotheses are tightened to BG — `U` is the specific
abelian Hall `(κ(M) ∪ σ(M))'`-factor of Proposition 14.2(a) and `R` is a *Sylow* `r`-subgroup
of `U` (`IsHallSubgroup {r}`), not an arbitrary `U ≤ M`, `R ≤ U` with `R ≠ ⊥` (under which the
conclusion fails).  The conclusion now also delivers `N_H(U) ⊄ M` (the FT-path clause consumed by
BG Theorem C(1) = `theoremC_paired_structure` conjunct 2): `N_H(U) = H ⊓ N_G(U) ≤ N_G(U)`, so
`N_H(U) ⊄ M ⟹ N_G(U) ⊄ M`.  The two remaining BG clauses `K ⊆ F(H ∩ M*)` and `σ(H)'-Hall(H)(H ∩ M*)`
(which require exposing the dual partner `M*` in the signature) are not consumed by any caller and
are omitted; the proof establishes `H ∩ M* = D` internally, so they are derivable if needed.
Translates the Coq `P2type_signalizer` (BGsection14.v L2243).  See `notes/bg/s14_typeP_counting.md`.
-/
theorem typeP2_neighbor_is_typeF_of_mem [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R H : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G))) :
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K ∧
      ¬ ((H ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ≤ M) ∧
      ∃ E E₁ E₂ E₃ : Subgroup G,
        OddOrder.BG.Ch3.S12.SubgroupESetup H E E₁ E₂ E₃ ∧ K ≤ E ∧
          K ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
  classical
  have hP : IsTypeP M := hP2.1
  haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hrprime : r.Prime := Fact.out
  have hRM : R ≤ M := hRU.trans hUM
  -- `r ∉ σ(M)`: `r ∈ π(U)` and `U` is a `(κ(M) ∪ σ(M))'`-Hall subgroup of `M`.
  have hrU' : r ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := hU.1 r hrU'
  have hrσM : r ∉ OddOrder.BG.Ch3.S10.sigma M := fun h => hrκσ (Or.inr h)
  -- `R ≠ ⊥`: `r ∣ |U|` and (Hall) `r ∤ [U : R]`, so `r ∣ |R|`.
  have hRne : R ≠ ⊥ := by
    have hlag : Nat.card ↥(R.subgroupOf U) * (R.subgroupOf U).index = Nat.card ↥U :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (R.subgroupOf U).index := fun hd =>
      hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
    have hrSub : r ∣ Nat.card ↥(R.subgroupOf U) :=
      ((Nat.Prime.dvd_mul hrprime).mp (by rw [hlag]; exact Nat.dvd_of_mem_primeFactors hr)).resolve_right
        hridx
    have hrR : r ∣ Nat.card ↥R := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv] at hrSub
    intro h; rw [h, Subgroup.card_bot] at hrR
    exact hrprime.one_lt.ne' (Nat.eq_one_of_dvd_one hrR ▸ rfl)
  -- Setup: the dual partner `M*` (Theorem 14.7 / `typeP_duality`).
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨Mst, hMstprop, hMstuniq⟩ := (typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, hMnc, hMstpair, hZcyc, hZti, hP2or, hcover⟩ := hMstprop
  -- `H ∈ 𝓜(N_G(R))` is now a hypothesis (`hH`); extract maximality and `N_G(R) ≤ H`.
  obtain ⟨hHmax, hNRH⟩ := mem_maximalSubgroupsContaining.mp hH
  -- `R ≤ H` (from `N_G(R) ≤ H`).
  have hRH : R ≤ H := (Subgroup.le_normalizer).trans hNRH
  -- `K ≤ H` (Coq `sEH`/`sKH`): `R = O_r(U)` is characteristic in abelian `U` (a normal Sylow
  -- `r`-subgroup), so `K ≤ N(U) ⟹ K ≤ N(R) ≤ H`.  Uses the `kappa_complement` structure
  -- (`group_set (U*K)`, here `hKNU : K ≤ N(U)`).
  have hUcomm : ∀ a b : ↥U, a * b = b * a := fun a b =>
    Subtype.ext (hUab (a : G) a.2 (b : G) b.2)
  -- `R = O_r(U)` is characteristic in abelian `U` (a normal Sylow `r`-subgroup), shared by
  -- `hKH`/`hUH`: `K, U ≤ N(U) ⟹ ≤ N(R) ≤ H`.
  have hRcardU : Nat.card ↥(R.subgroupOf U) = r ^ (Nat.card ↥U).factorization r := by
    have hpow : Nat.card ↥(R.subgroupOf U)
        = r ^ (Nat.card ↥(R.subgroupOf U)).factorization r := by
      apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
      apply Finsupp.ext; intro q; rw [Finsupp.single_apply]
      by_cases hq : r = q
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        by_cases hqp : q.Prime
        · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
          have hmem : q ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Nat.card_pos.ne'⟩
          exact (Set.mem_singleton_iff.mp (hR.1 q hmem)).symm
        · exact Nat.factorization_eq_zero_of_not_prime _ hqp
    have hfact : (Nat.card ↥U).factorization r
        = (Nat.card ↥(R.subgroupOf U)).factorization r := by
      have hidx : (R.subgroupOf U).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
      have hlag := Subgroup.card_mul_index (R.subgroupOf U)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidx, add_zero]
    rw [hfact]; exact hpow
  have hRUnorm : (R.subgroupOf U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have heq : g * n * g⁻¹ = n := by
      calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [hUcomm g n]
        _ = n := by group
    rw [heq]; exact hn
  haveI hPchar : (R.subgroupOf U).Characteristic := by
    have hPn : ((Sylow.ofCard (R.subgroupOf U) hRcardU : Sylow r ↥U) : Subgroup ↥U).Normal := by
      rw [Sylow.coe_ofCard]; exact hRUnorm
    have h := Sylow.characteristic_of_normal (Sylow.ofCard (R.subgroupOf U) hRcardU) hPn
    rwa [Sylow.coe_ofCard] at h
  have hKH : K ≤ H := fun k hk => hNRH (by
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := U) (C := R.subgroupOf U) (hKNU hk)
    rwa [Subgroup.map_subgroupOf_eq_of_le hRU] at hmem)
  have hUH : U ≤ H := fun u hu => hNRH (by
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic
      (W := U) (C := R.subgroupOf U) (Subgroup.le_normalizer hu)
    rwa [Subgroup.map_subgroupOf_eq_of_le hRU] at hmem)
  -- `H` is not conjugate to `M` (`r ∈ σ(H) ∖ σ(M)`) nor to its partner `M*` (coprime `K`/`R`).
  -- These two non-conjugacies drive both the type-`F` classification and `σ(H)'`-membership of `K`.
  have notMGH : ¬ IsConjugateSubgroup H M := by
    rintro ⟨a, ha⟩
    -- `|R| = r ^ (|U|).factorization r` (`R` is a Sylow `r`-subgroup of `U`).
    have hSU : Nat.card ↥(R.subgroupOf U) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
    have hRpow : Nat.card ↥R = r ^ (Nat.card ↥R).factorization r := by
      apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
      apply Finsupp.ext
      intro q
      rw [Finsupp.single_apply]
      by_cases hq : r = q
      · rw [if_pos hq, hq]
      · rw [if_neg hq]
        by_cases hqp : q.Prime
        · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
          have hmem : q ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hqp, hSU ▸ hdvd, Nat.card_pos.ne'⟩
          exact (Set.mem_singleton_iff.mp (hR.1 q hmem)).symm
        · exact Nat.factorization_eq_zero_of_not_prime _ hqp
    -- `(|U|).factorization r = (|R|).factorization r` (`r ∤ [U : R]`).
    have hfUR : (Nat.card ↥U).factorization r = (Nat.card ↥R).factorization r := by
      have hidxU : (R.subgroupOf U).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
      have hlag := Subgroup.card_mul_index (R.subgroupOf U)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidxU, add_zero, hSU]
    -- `(|U|).factorization r = (|M|).factorization r` (`r ∤ [M : U]`).
    have hfUM : (Nat.card ↥U).factorization r = (Nat.card ↥M).factorization r := by
      have hidxM : (U.subgroupOf M).index.factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
          hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrκσ)
      have hUcard : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
      have hlag := Subgroup.card_mul_index (U.subgroupOf M)
      rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hidxM, add_zero, hUcard]
    -- `|H| = |M|` (conjugate subgroups).
    have hcardHM : Nat.card ↥H = Nat.card ↥M := by
      rw [← ha]; exact (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm
    -- `R` is a Sylow `r`-subgroup of `H`.
    have hRsylH : Nat.card ↥(R.subgroupOf H) = r ^ (Nat.card ↥H).factorization r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv, hcardHM, ← hfUM, hfUR]
      exact hRpow
    -- `r ∈ σ(H)` (`R` Sylow `r` of `H`, `N_G(R) ≤ H`), hence `r ∈ σ(M)` (conjugacy), contradiction.
    have hrH : r ∈ (Nat.card ↥H).primeFactors := by
      rw [hcardHM]
      exact Nat.mem_primeFactors.mpr ⟨hrprime,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hUM), Nat.card_pos.ne'⟩
    have hrσH : r ∈ OddOrder.BG.Ch3.S10.sigma H := by
      rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
      refine ⟨hrH, Sylow.ofCard (R.subgroupOf H) hRsylH, ?_⟩
      rw [Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hRH]
      exact hNRH
    exact hrσM (by have h := OddOrder.BG.Ch3.S10.sigma_conj (M := H) a hrσH; rwa [ha] at h)
  have notMstGH : ¬ IsConjugateSubgroup H Mst := by
    -- `M_σ ∩ M* = K*` (the embedding's conjunct (d) kernel, avoiding the σ(M)-Hall-of-M* clause).
    have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst :=
      (le_of_eq hMstpair.2.2).trans inf_le_left
    have hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mst = Kstar :=
      msigma_inf_partner_eq_kstar hG hM hP2 hKM hKstardef hMstmax hKMsigmaMst hMstpair.1 hMnc
    have hKstarM : Kstar ≤ M := by
      rw [hKstardef]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hKstarNe : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstardef hU).2.1
    have hKNe : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
    -- `ziMMst : M ⊓ M* = K ⊔ K*` and `sK_uniqMst : K ≤ M*^a ⟹ a ∈ M*`.
    obtain ⟨hziMMst, hsKuniq⟩ := partner_inf_and_uniq hG hMstmax hMstP hMstpair.1 hMstpair.2.1
      hMstpair.2.2 hKMsigmaMst hKM hKstarM hZcyc hKstarNe hKNe hMsMst
    -- `r ∤ |Z|`: `Z = K ⊔ K* = K · K*` (disjoint, commuting), `r ∉ π(K) ⊆ κ(M)`, `r ∉ π(K*) ⊆ σ(M)`.
    have hKπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)ᶜ K :=
      kappaHall_isPiSubgroup_sigmaCompl hKM hK
    have hKstarπ : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M) Kstar :=
      Kstar_isPiSubgroup_sigma hKstardef
    have hrnK : ¬ r ∣ Nat.card ↥K := fun hd => (fun h => hrκσ (Or.inl h))
      (hK.1 r (Nat.mem_primeFactors.mpr ⟨hrprime, by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]; exact hd, Nat.card_pos.ne'⟩))
    have hrnKstar : ¬ r ∣ Nat.card ↥Kstar := fun hd =>
      hrσM (hKstarπ r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Nat.card_pos.ne'⟩))
    have hKKstar_bot : K ⊓ Kstar = ⊥ := by
      rw [← Subgroup.card_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpσc := hKπ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
      have hpσ := hKstarπ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpd.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩)
      exact hpσc hpσ
    have hKcKstar : K ≤ Subgroup.centralizer (Kstar : Set G) := by
      haveI := hZcyc
      letI : CommGroup ↥(K ⊔ Kstar) := IsCyclic.commGroup
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (mul_comm (⟨s, Subgroup.mem_sup_right hs⟩ : ↥(K ⊔ Kstar))
        (⟨k, Subgroup.mem_sup_left hk⟩))
    have hcardZ : Nat.card ↥(K ⊔ Kstar) = Nat.card ↥K * Nat.card ↥Kstar :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint
        (hKcKstar.trans (Subgroup.centralizer_le_normalizer _)) hKKstar_bot
    have hrnZ : ¬ r ∣ Nat.card ↥(K ⊔ Kstar) := by
      rw [hcardZ]; exact fun hd => (hrprime.dvd_mul.mp hd).elim hrnK hrnKstar
    have hrR : r ∣ Nat.card ↥R := by
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
        (show Nat.card ↥R ≠ 1 from fun h => hRne (Subgroup.card_eq_one.mp h))
      have hpmem : p ∈ (Nat.card ↥(R.subgroupOf U)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv]; exact hpd, Nat.card_pos.ne'⟩
      exact (Set.mem_singleton_iff.mp (hR.1 p hpmem)) ▸ hpd
    -- If `H` were conjugate to `M*`, then `K ≤ H` and `sK_uniqMst` force `H = M*`, so
    -- `R ≤ M ⊓ M* = Z`, whence `r ∣ |Z|`, contradicting `r ∤ |Z|`.
    rintro ⟨a, ha⟩
    have hHeq : H = MulAut.conj a⁻¹ • Mst := by
      rw [← ha, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have haInvMst : a⁻¹ ∈ Mst := hsKuniq a⁻¹ (hHeq ▸ hKH)
    have hHMst : H = Mst := hHeq.trans (Subgroup.conj_smul_eq_self_of_mem haInvMst)
    have hRZ : R ≤ K ⊔ Kstar := hziMMst ▸ le_inf hRM (hHMst ▸ hRH)
    exact hrnZ (hrR.trans (Subgroup.card_dvd_of_le hRZ))
  -- ═══ Shared σ-decomposition infrastructure for conjuncts 2/3/4 (Coq `P2type_signalizer`) ═══
  -- Conjunct 1 (`IsTypeF H`), hoisted (also the `hF` input to Lemma 14.11 below): every type-`P`
  -- maximal is conjugate to `M` or `M*` (`hcover`), and `H` is conjugate to neither.
  have hFmaxH : IsTypeF H := by
    show kappa H = ∅
    rw [← Set.not_nonempty_iff_eq_empty]
    intro hHP
    exact (hcover H hHmax hHP).elim notMGH notMstGH
  -- `|K| = q` is prime (Prop 14.2(g), type-`P₂`), so `K` is cyclic of prime order.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard, by rw [hKcard, pow_one]⟩
  -- `defUK : ⁅U, K⁆ = U` (BG `defUK`).
  have defUK : (⁅U, K⁆ : Subgroup G) = U :=
    typeP2_kappaHall_commutator_eq_self hG hM hP2 hKM hUM hK hKstardef hU hUab hKNU
  -- `K ≤ M*_σ` and `K` is a `σ(H)'`-group (Thm 13.9: `σ(H) ∩ σ(M*) = ∅`, `H` not conj. to `M*`).
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst := hMstpair.2.2.le.trans inf_le_left
  have hHMstdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma H) (OddOrder.BG.Ch3.S10.sigma Mst) :=
    sigma_disjoint_of_nonconjugate hG hHmax hMstmax notMstGH
  have hsH_K : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma H)ᶜ K := by
    intro p hp
    rw [Set.mem_compl_iff]
    intro hpσH
    exact (Set.disjoint_left.mp hHMstdisj) hpσH
      (OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hKMsigmaMst) Nat.card_pos.ne' hp))
  -- `E`: a `σ(H)'`-Hall (E-setup) complement of `H_σ` in `H`, containing `K` (`Hall_superset`).
  obtain ⟨E, E₁, E₂, E₃, hEsetup, hKE, hE_pi⟩ :=
    OddOrder.BG.Ch3.S12.exists_subgroupESetup_with_le hG hHmax hKH hsH_K
  -- `q = |K| ∈ σ(M*)` (`K ≤ M*_σ`).
  have hqσMst : q ∈ OddOrder.BG.Ch3.S10.sigma Mst :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mst q
      (Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKMsigmaMst,
        Nat.card_pos.ne'⟩)
  -- `𝓜(C(K)) = {Mst}` (Prop 14.2(d) for `Mst`, whose dual `K*` is `K`): `typeP_structure`
  -- conjunct 6 with the rank-one `K ∈ ℰ_q¹`.
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    haveI hMstsol : IsSolvable ↥Mst := hG.solvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  -- `K ⊆ F(E)` (Coq `sK_FD`): otherwise Lemma 14.11 (`exists_maximal_of_typeF_notMem_fitting`)
  -- produces a maximal `M'` with `q ∈ τ₂(M')` and `𝓜(C(K)) = {M'}` (⟹ `M' = Mst`, but
  -- `q ∈ τ₂(Mst) ∩ σ(Mst) = ∅`), or `q ∈ κ(M')` with `M'` type-`P₁` (⟹ `M' ∼ M` makes `M`
  -- type-`P₁` against `M ∈ 𝓜_{P₂}`, or `M' ∼ Mst` gives `q ∈ κ(Mst) ⊆ σ(Mst)ᶜ`).
  have hsK_FE : K ≤ OddOrder.BG.Ch2.S08.fittingInG E := by
    by_contra hnotKFE
    have hqpiE : q ∈ piSet E :=
      Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKE, Nat.card_pos.ne'⟩
    obtain ⟨Mstar', hMstar'max, hdich⟩ := exists_maximal_of_typeF_notMem_fitting hG hHmax hFmaxH
      hEsetup.isComplement'_subgroupOf hEsetup.E_le hqpiE hKelemq hKE hnotKFE
    rcases hdich with ⟨hqτ2, huniq'⟩ | ⟨hqκ', hP1'⟩
    · -- Case 1: `Mstar' = Mst` (both `= 𝓜(C(K))`), but `q ∈ τ₂(Mst)` and `q ∈ σ(Mst)`.
      have hMstar'eq : Mstar' = Mst :=
        Set.singleton_eq_singleton_iff.mp (huniq'.symm.trans huniqMst)
      exact tau2_subset_sigma_compl Mst (hMstar'eq ▸ hqτ2) hqσMst
    · -- Case 2: `Mstar'` type-`P₁`; `hcover` makes it conjugate to `M` or `Mst`.
      rcases hcover Mstar' hMstar'max hP1'.1 with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact not_isTypeP1_and_isTypeP2 ⟨hb ▸ (isTypeP1_conj_smul b Mstar').mpr hP1', hP2⟩
      · refine kappa_subset_sigmaCompl (M := Mst) ?_ hqσMst
        rw [← hb, kappa_conj_smul]; exact hqκ'
  -- ═══ Conjunct 2 (`U ≤ M_σ(H)`, Coq `sUHs`), hoisted: also feeds `U ⊆ F(H)` for conjuncts 3/4 ═══
  -- `U = ⁅U,K⁆ ≤ HsDq := M_σ(H) ⊔ O_q(F(E))`, and `M_σ(H)` is the normal `{q}'`-Hall of `HsDq`.
  have hUMsH : U ≤ OddOrder.BG.Ch3.S10.Msigma H := by
    classical
    -- `q ∈ κ(M)`, `q ∉ σ(H)`, and `|U|` is a `{q}'`-number.
    have hqκM : q ∈ kappa M := hK.1 q (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hKcard]
      exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
    have hqσ'H : q ∉ OddOrder.BG.Ch3.S10.sigma H :=
      hsH_K q (by rw [hKcard]; exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
    have hUq' : ∀ p ∈ (Nat.card ↥U).primeFactors, p ∈ ({q}ᶜ : Set ℕ) := by
      intro p hp hpq
      exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
        (Or.inl ((Set.mem_singleton_iff.mp hpq) ▸ hqκM))
    -- `O_q(F(E))`, `K ≤ O_q(F(E))`, `E ≤ N(O_q(F(E)))`.
    set Oq : Subgroup G := opiCoreInG ({q} : Set ℕ)
      (OddOrder.BG.Ch2.S08.fittingInG E) with hOqdef
    have hOqE : Oq ≤ E := (opiCoreInG_le _ _).trans
      (OddOrder.BG.Ch2.S08.fittingInG_le E)
    have hKOq : K ≤ Oq := OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E) hsK_FE (IsPGroup.of_card (by rw [hKcard, pow_one]))
    have hOqpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Oq :=
      isPiSubgroup_opiCoreInG _ _
    have hEnOq : E ≤ Subgroup.normalizer (Oq : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hOqE]
      exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal _ _
    -- `HsDq := M_σ(H) ⊔ O_q(F(E))`; `M_σ(H) ◁ H`, `HsDq ≤ H`, `H ≤ N(HsDq)`.
    set HsDq : Subgroup G := OddOrder.BG.Ch3.S10.Msigma H ⊔ Oq with hHsDqdef
    have hHsDqH : HsDq ≤ H := sup_le (OddOrder.BG.Ch3.S10.Msigma_le H) (hOqE.trans hEsetup.E_le)
    haveI hMsHnorm : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hHnMsH : H ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le H)).mp hMsHnorm
    have hHnHsDq : H ≤ Subgroup.normalizer (HsDq : Set G) := by
      calc H = OddOrder.BG.Ch3.S10.Msigma H ⊔ E := hEsetup.E_compl_sup.symm
        _ ≤ Subgroup.normalizer (HsDq : Set G) :=
          sup_le (le_sup_left.trans Subgroup.le_normalizer)
            (le_normalizer_sup (hEsetup.E_le.trans hHnMsH) hEnOq)
    -- `U = ⁅U,K⁆ ≤ ⁅H, HsDq⁆ ≤ HsDq` (since `HsDq ◁ H`).
    have hUHsDq : U ≤ HsDq := by
      rw [← defUK]
      refine (Subgroup.commutator_mono hUH (hKOq.trans (le_sup_right : Oq ≤ HsDq))).trans ?_
      rw [Subgroup.commutator_comm H HsDq]
      exact Ch04.commutator_le_of_le_normalizer hHnHsDq
    -- `M_σ(H) ⊓ Oq = ⊥` (`σ(H)` vs `{q}`, `q ∉ σ(H)`), so `|HsDq| = |M_σ(H)|·|Oq|`.
    have hMsOqbot : OddOrder.BG.Ch3.S10.Msigma H ⊓ Oq = ⊥ := by
      apply Subgroup.inf_eq_bot_of_coprime
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := OddOrder.BG.Ch3.S10.sigma H)
        Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => OddOrder.BG.Ch3.S10.Msigma_isPiGroup H p hp)
        (fun p hp hpσ => ?_)
      exact hqσ'H ((Set.mem_singleton_iff.mp (hOqpi p hp)) ▸ hpσ)
    have hcardHsDq : Nat.card ↥HsDq = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma H) * Nat.card ↥Oq := by
      have hOqnMs : Oq ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma H : Set G) :=
        (hOqE.trans hEsetup.E_le).trans hHnMsH
      have h := card_sup_eq_mul_of_le_normalizer_of_disjoint hOqnMs (by rw [inf_comm]; exact hMsOqbot)
      rw [hHsDqdef, sup_comm, h, Nat.mul_comm]
    -- `M_σ(H)` is the normal `{q}'`-Hall of `HsDq`.
    haveI hMsHsDqnorm : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (hHsDqH.trans hHnMsH)
    have hidxOq : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq).index = Nat.card ↥Oq := by
      have hlag := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)).toEquiv, hcardHsDq] at hlag
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hlag
    have hMsHall : Ch03.IsHallSubgroup ({q}ᶜ : Set ℕ)
        ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf HsDq) := by
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)).toEquiv] at hp
        exact fun hpq => hqσ'H ((Set.mem_singleton_iff.mp hpq) ▸
          OddOrder.BG.Ch3.S10.Msigma_isPiGroup H p hp)
      · rw [hidxOq] at hp
        exact fun hpc => hpc (hOqpi p hp)
    have hUpi : Ch03.Subgroup.IsPiGroup ({q}ᶜ : Set ℕ) (U.subgroupOf HsDq) := by
      intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUHsDq).toEquiv] at hp
      exact hUq' p hp
    have hfinal := OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hMsHall hUpi
    have hmapped := Subgroup.map_mono (f := HsDq.subtype) hfinal
    rwa [Subgroup.map_subgroupOf_eq_of_le hUHsDq, Subgroup.map_subgroupOf_eq_of_le
      (le_sup_left : OddOrder.BG.Ch3.S10.Msigma H ≤ HsDq)] at hmapped
  -- ═══ Shared structure for conjuncts 3/4: `H_σ ⊆ F(H)` and `Fu = O_{(κ∪σ)'(M)}(F(H))` ═══
  -- `q ∉ σ(H)` (`K` is a `σ(H)'`-group, `q ∣ |K|`) and `q ∈ π(H)` (`K ≤ H`, `|K| = q`).
  have hqσ'H : q ∉ OddOrder.BG.Ch3.S10.sigma H :=
    hsH_K q (by rw [hKcard]; exact Nat.mem_primeFactors.mpr ⟨hqprime, dvd_rfl, hqprime.pos.ne'⟩)
  have hqπH : q ∈ piSet H :=
    Nat.mem_primeFactors.mpr ⟨hqprime, hKcard ▸ Subgroup.card_dvd_of_le hKH, Nat.card_pos.ne'⟩
  -- `H_σ ⊆ F(H)` (Coq `sHsFH`): `H` is type-`F`, so `q ∉ κ(H) = ∅`; Lemma 14.1
  -- (`msigma_structure_of_notMem_sigma_kappa`) with a maximal-rank elementary abelian `q`-subgroup
  -- of `H` makes `M_σ(H)` nilpotent, hence `≤ F(H)`.
  have hHsFH : OddOrder.BG.Ch3.S10.Msigma H ≤ OddOrder.BG.Ch2.S08.fittingInG H := by
    have hκH : kappa H = ∅ := hFmaxH
    have hqκH : q ∉ kappa H := by rw [hκH]; exact Set.notMem_empty q
    obtain ⟨B, hBea, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥H) (p := q) (n := pRank ↥H q)
      (OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hqπH) (le_refl _)
    obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
    have hjeq : j = pRank ↥H q := by
      have hsq := le_antisymm (le_pRank B hBea) hBlog
      rwa [hj, Nat.log_pow hqprime.one_lt] at hsq
    have hAmem : B.map H.subtype ∈ elemAbelianOfRank G q (pRank ↥H q) :=
      ⟨Subgroup.IsElementaryAbelian.map H.subtype_injective hBea, by
        rw [Subgroup.card_map_of_injective H.subtype_injective, hj, hjeq]⟩
    have hAH : B.map H.subtype ≤ H := Subgroup.map_subtype_le _
    haveI h1 : ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    haveI h2 : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma H) :=
      (msigma_structure_of_notMem_sigma_kappa hG hHmax hqπH hqσ'H hqκH hAmem hAH).2.2
    haveI h3 : Group.IsNilpotent ↥((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le H)).symm
    have h4 : (OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H ≤ OddOrder.Isaacs.Ch01.fitting ↥H :=
      OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    calc OddOrder.BG.Ch3.S10.Msigma H
        = ((OddOrder.BG.Ch3.S10.Msigma H).subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le H)).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥H).map H.subtype := Subgroup.map_mono h4
      _ = OddOrder.BG.Ch2.S08.fittingInG H := rfl
  -- `Fu := O_{(κ(M)∪σ(M))'}(F(H))`: normal in `H`, contains `U`, and `M ⊓ Fu = U` (Coq `defU`).
  set π : Set ℕ := (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ with hπdef
  set Fu : Subgroup G := opiCoreInG π (OddOrder.BG.Ch2.S08.fittingInG H) with hFudef
  haveI hFHnil : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG H) :=
    OddOrder.BG.Ch2.S08.fittingInG_isNilpotent H
  have hUFH : U ≤ OddOrder.BG.Ch2.S08.fittingInG H := hUMsH.trans hHsFH
  have hUπ : Ch03.Subgroup.IsPiGroup π U := by
    intro p hp
    exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
  have hUFu : U ≤ Fu := by
    have hUFHpi : Ch03.Subgroup.IsPiGroup π (U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H)) :=
      Ch03.Subgroup.IsPiGroup.subgroupOf hUFH hUπ
    have hHall : Ch03.IsHallSubgroup π
        (Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H)) :=
      OddOrder.BG.Ch3.S10.oPiCore_isHall_of_isNilpotent _
    have hle : U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H) ≤
        Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H) :=
      OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hHall hUFHpi
    calc U = (U.subgroupOf (OddOrder.BG.Ch2.S08.fittingInG H)).map
              (OddOrder.BG.Ch2.S08.fittingInG H).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hUFH).symm
      _ ≤ (Ch03.oPiCore π ↥(OddOrder.BG.Ch2.S08.fittingInG H)).map
              (OddOrder.BG.Ch2.S08.fittingInG H).subtype := Subgroup.map_mono hle
      _ = Fu := rfl
  have hFuH : Fu ≤ H :=
    (opiCoreInG_le _ _).trans (OddOrder.BG.Ch2.S08.fittingInG_le H)
  have hHnFu : H ≤ Subgroup.normalizer (Fu : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hFuH]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal π H
  have hdefU : M ⊓ Fu = U := by
    refine le_antisymm ?_ (le_inf hUM hUFu)
    -- `V := M ⊓ Fu` is a `π`-subgroup of `M` containing the `π`-Hall `U`, so `V = U` (cardinality).
    have hVπ : ∀ p ∈ (Nat.card ↥(M ⊓ Fu)).primeFactors, p ∈ π := by
      intro p hp
      exact (isPiSubgroup_opiCoreInG _ (OddOrder.BG.Ch2.S08.fittingInG H)) p
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_right) Nat.card_pos.ne' hp)
    have hlag : Nat.card ↥U * (U.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
      exact Subgroup.card_mul_index _
    have hcop : Nat.Coprime (Nat.card ↥(M ⊓ Fu)) (U.subgroupOf M).index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpd
      exact (hU.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpd.2, Subgroup.index_ne_zero_of_finite⟩))
        (hVπ p (Nat.mem_primeFactors.mpr ⟨hp, hpd.1, Nat.card_pos.ne'⟩))
    have hVdvdU : Nat.card ↥(M ⊓ Fu) ∣ Nat.card ↥U :=
      hcop.dvd_of_dvd_mul_right (hlag ▸ Subgroup.card_dvd_of_le inf_le_left)
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hUM hUFu)
      (Nat.le_of_dvd Nat.card_pos hVdvdU)).symm.le
  refine ⟨hFmaxH, hUMsH, ?_, ?_, E, E₁, E₂, E₃, hEsetup, hKE, hsK_FE⟩
  · -- Conjunct 3 (`M ⊓ H = U ⊔ K`, Coq L2375-2380): `⊇` is immediate; `⊆` is
    -- `M ⊓ H ⊆ N_M(U) = U ⊔ K` (`defNMU`, BG 6.5(b): `M = M_σ ⋊ (U⊔K)`, `C_{M_σ}(U) = 1`).
    classical
    refine le_antisymm ?_ (sup_le (le_inf hUM hUH) (le_inf hKM hKH))
    -- σ-decomposition `M = M_σ ⊔ (U ⊔ K)`: the σ-Hall `M_σ`, the κ-Hall `K`, and the
    -- `(κ∪σ)'`-Hall `U` cover all primes, so the index of their join in `M` has no prime divisor.
    have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
      OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
        (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
    have hJleM : OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) ≤ M :=
      sup_le (OddOrder.BG.Ch3.S10.Msigma_le M) (sup_le hUM hKM)
    have hJM : OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) = M := by
      have hidx1 : ((OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K)).subgroupOf M).index = 1 := by
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hsub : ∀ S : Subgroup G, S ≤ OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K) →
            p ∈ (S.subgroupOf M).index.primeFactors := by
          intro S hSJ
          refine Nat.mem_primeFactors.mpr ⟨hp, ?_, Subgroup.index_ne_zero_of_finite⟩
          exact hpdvd.trans (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono M hSJ))
        have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
          hMσHall.2 p (hsub _ le_sup_left)
        have hpκσc : p ∉ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
          hU.2 p (hsub _ (le_sup_right.trans' le_sup_left))
        have hpκ : p ∉ kappa M := hK.2 p (hsub _ (le_sup_right.trans' le_sup_right))
        exact hpκσc (Set.mem_compl (fun h => h.elim hpκ hpσ))
      have htop : (OddOrder.BG.Ch3.S10.Msigma M ⊔ (U ⊔ K)).subgroupOf M = ⊤ :=
        Subgroup.index_eq_one.mp hidx1
      exact le_antisymm hJleM (Subgroup.subgroupOf_eq_top.mp htop)
    -- `C_{M_σ}(U) = ⊥` (Lemma 14.1): `R` is a Sylow `r`-subgroup of `M` (`r ∈ (κ∪σ)'`, `U` Hall),
    -- so a maximal-rank elementary abelian `A ≤ R ≤ U` makes `M_σ ⊓ C(A) = ⊥`; antitonicity lifts
    -- this to `M_σ ⊓ C(U) ≤ M_σ ⊓ C(A) = ⊥`.
    have hRM : R ≤ M := hRU.trans hUM
    have hrπM : r ∈ piSet M :=
      Nat.mem_primeFactors.mpr ⟨hrprime,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hUM), Nat.card_pos.ne'⟩
    have hCMsU : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
      have hSU : Nat.card ↥(R.subgroupOf U) = Nat.card ↥R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv
      have hRpow : Nat.card ↥R = r ^ (Nat.card ↥R).factorization r := by
        apply Nat.eq_pow_of_factorization_eq_single Nat.card_pos.ne'
        apply Finsupp.ext; intro q; rw [Finsupp.single_apply]
        by_cases hq : r = q
        · rw [if_pos hq, hq]
        · rw [if_neg hq]
          by_cases hqp : q.Prime
          · refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hq ?_)
            exact (Set.mem_singleton_iff.mp (hR.1 q (Nat.mem_primeFactors.mpr
              ⟨hqp, hSU ▸ hdvd, Nat.card_pos.ne'⟩))).symm
          · exact Nat.factorization_eq_zero_of_not_prime _ hqp
      have hfUR : (Nat.card ↥U).factorization r = (Nat.card ↥R).factorization r := by
        have hidxU : (R.subgroupOf U).index.factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
            hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl)
        have hlag := Subgroup.card_mul_index (R.subgroupOf U)
        rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidxU, add_zero, hSU]
      have hfUM : (Nat.card ↥U).factorization r = (Nat.card ↥M).factorization r := by
        have hidxM : (U.subgroupOf M).index.factorization r = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hdvd =>
            hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrκσ)
        have hUcard : Nat.card ↥(U.subgroupOf M) = Nat.card ↥U :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv
        have hlag := Subgroup.card_mul_index (U.subgroupOf M)
        rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply, hidxM, add_zero, hUcard]
      have hRsylM : Nat.card ↥(R.subgroupOf M) = r ^ (Nat.card ↥M).factorization r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hRpow, ← hfUR, hfUM]
      have hpRankRM : pRank ↥R r = pRank ↥M r := by
        have h1 : pRank ↥(R.subgroupOf M) r = pRank ↥M r := by
          have := pRank_sylow_eq (Sylow.ofCard (R.subgroupOf M) hRsylM)
          rwa [Sylow.coe_ofCard] at this
        rw [← h1]; exact pRank_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hRM).symm r
      have hRrankpos : 0 < pRank ↥R r := by
        rw [hpRankRM]; exact OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hrπM
      obtain ⟨B, hBea, hBlog⟩ := exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
        (G := ↥R) (p := r) (n := pRank ↥R r) hRrankpos (le_refl _)
      obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
      have hjeq : j = pRank ↥R r := by
        have hsq := le_antisymm (le_pRank B hBea) hBlog
        rwa [hj, Nat.log_pow hrprime.one_lt] at hsq
      have hAR : B.map R.subtype ≤ R := Subgroup.map_subtype_le _
      have hAmem : B.map R.subtype ∈ elemAbelianOfRank G r (pRank ↥M r) :=
        ⟨Subgroup.IsElementaryAbelian.map R.subtype_injective hBea, by
          rw [Subgroup.card_map_of_injective R.subtype_injective, hj, hjeq, hpRankRM]⟩
      have hrκ : r ∉ kappa M := fun h => hrκσ (Or.inl h)
      exact (msigma_centralizer_eq_bot_of_elemAb_le hG hM hrπM hrσM hrκ hAmem
        (hAR.trans hRM) (hAR.trans hRU)).1
    -- `M ⊓ H ⊆ N_M(U)` (geometric: `M ⊓ H ≤ N(M) ⊓ N(Fu) ≤ N(M ⊓ Fu) = N(U)`).
    have hMHnU : M ⊓ H ≤ Subgroup.normalizer (U : Set G) := by
      rw [← hdefU]
      exact le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
        (inf_le_right.trans hHnFu)
    -- `defNMU`: BG 6.5(b) in `↥M` gives `N_{↥M}(U) = (C(U) ⊓ M_σ) · (N(U) ⊓ (U⊔K))`; the
    -- first factor is `C_{M_σ}(U) = 1`, so every `n ∈ N_M(U)` lies in `U ⊔ K`.
    have hKU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ⊔ (U ⊔ K).subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) (sup_le hUM hKM), hJM,
        Subgroup.subgroupOf_self]
    have hcop : Nat.Coprime (Nat.card ↥(U.subgroupOf M))
        (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hpd
      have hpU : p ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
        hU.1 p (Nat.mem_primeFactors.mpr ⟨hp, hpd.1, Nat.card_pos.ne'⟩)
      refine hpU (Or.inr (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p ?_))
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpd.2, Nat.card_pos.ne'⟩
    haveI hMsol : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups hM
    haveI hMσMnorm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hlem := OddOrder.BG.Ch1.S06.normalizer_eq_centralizerK_mul_normalizerU (G := ↥M)
      (K := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U := (U ⊔ K).subgroupOf M)
      (H := U.subgroupOf M) hKU (Subgroup.subgroupOf_mono M le_sup_left) hcop
    -- The first factor `C(U) ⊓ M_σ` is trivial in `↥M` (`C_{M_σ}(U) = 1`).
    have hfactor1 : Subgroup.centralizer ((U.subgroupOf M : Subgroup ↥M) : Set ↥M) ⊓
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_inf] at hc
      have hcCU : (M.subtype c) ∈ Subgroup.centralizer (U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u huU
        have hcomm := (Subgroup.mem_centralizer_iff.mp hc.1) (⟨u, hUM huU⟩ : ↥M)
          (Subgroup.mem_subgroupOf.mpr huU)
        have := congrArg (M.subtype) hcomm
        simpa using this
      have hmem : (M.subtype c) ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (U : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp hc.2, hcCU⟩
      rw [hCMsU, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact M.subtype_injective (by rw [hmem, map_one])
    -- Conclude: `M ⊓ H ⊆ M ⊓ N_G(U)`, and each such `n` lies in `U ⊔ K`.
    refine le_trans (le_inf inf_le_left hMHnU) ?_
    intro n hn
    rw [Subgroup.mem_inf] at hn
    obtain ⟨hnM, hnNU⟩ := hn
    have hnbar : (⟨n, hnM⟩ : ↥M) ∈ Subgroup.normalizer (U.subgroupOf M) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hUM, Subgroup.mem_subgroupOf]; exact hnNU
    have hnbarc := SetLike.mem_coe.mpr hnbar
    rw [hlem] at hnbarc
    obtain ⟨c, hc, u, hu, hcu⟩ := Set.mem_mul.mp hnbarc
    have hc1 : c = 1 :=
      Subgroup.mem_bot.mp (hfactor1 ▸ SetLike.mem_coe.mp hc)
    rw [hc1, one_mul] at hcu
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hu
    have hnUK : (M.subtype u) ∈ U ⊔ K := Subgroup.mem_subgroupOf.mp hu.2
    rw [hcu] at hnUK
    simpa using hnUK
  · -- Conjunct 4 (`N_H(U) ⊄ M`): suppose `N_H(U) = H ⊓ N_G(U) ≤ M`.  Then `N_Fu(U) = N_G(U) ⊓ Fu`
    -- lies in `M ⊓ Fu = U`, so `U` is self-normalizing in the nilpotent `Fu`, forcing `Fu = U`.
    -- Hence `H ≤ N_G(Fu) = N_G(U)`, so `H = H ⊓ N_G(U) ≤ M`, whence `H = M` (both maximal),
    -- contradicting `H` not conjugate to `M`.
    intro hNHU_M
    have hNFuU : Subgroup.normalizer (U : Set G) ⊓ Fu ≤ U := by
      have h1 : Subgroup.normalizer (U : Set G) ⊓ Fu ≤ M :=
        le_trans (le_inf (le_trans inf_le_right hFuH) inf_le_left) hNHU_M
      calc Subgroup.normalizer (U : Set G) ⊓ Fu ≤ M ⊓ Fu := le_inf h1 inf_le_right
        _ = U := hdefU
    haveI hFunil : Group.IsNilpotent ↥Fu :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe
        (opiCoreInG_le π (OddOrder.BG.Ch2.S08.fittingInG H)))
    have hFuU : Fu = U := eq_of_isNilpotent_normalizer_inf_le hFunil hUFu hNFuU
    have hHnU : H ≤ Subgroup.normalizer (U : Set G) := hFuU ▸ hHnFu
    have hHM : H ≤ M := le_trans (le_inf le_rfl hHnU) hNHU_M
    have hHeqM : H = M := by
      rcases lt_or_eq_of_le hHM with hlt | heq
      · exact absurd ((mem_maximalSubgroups.mp hHmax).2 M hlt) (mem_maximalSubgroups.mp hM).1
      · exact heq
    exact notMGH (by rw [hHeqM])

/-- **BG Corollary 14.12** (mmd L4230), existential form.  For a type-`P₂` maximal `M` with
`κ`-complement `K` and abelian Hall `(κ ∪ σ)′`-factor `U`, and a Sylow `r`-subgroup `R ≤ U`,
there is a maximal `H ⊇ N_G(R)` that is type-`F`, with `U ≤ H_σ`, `M ⊓ H = U ⊔ K`, and
`N_H(U) ⊄ M`.

Convenience wrapper over `typeP2_neighbor_is_typeF_of_mem`: it picks `H` as a maximal overgroup
of `N_G(R)` (via `eq_top_or_exists_le_coatom`) and drops the `E`-setup export.  Consumers needing
the σ(H)′-Hall `E` / `K ⊆ F(E)` clauses (Theorem 15.8) call `_of_mem` with their own `H`. -/
theorem typeP2_neighbor_is_typeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G)) :
    ∃ H : Subgroup G,
      H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) ∧
      IsTypeF H ∧ U ≤ OddOrder.BG.Ch3.S10.Msigma H ∧ M ⊓ H = U ⊔ K ∧
      ¬ ((H ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) ≤ M) := by
  classical
  haveI : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hrprime : r.Prime := Fact.out
  have hRM : R ≤ M := hRU.trans hUM
  -- `R ≠ ⊥`: `r ∣ |U|` and (Hall) `r ∤ [U : R]`, so `r ∣ |R|`.
  have hRne : R ≠ ⊥ := by
    have hlag : Nat.card ↥(R.subgroupOf U) * (R.subgroupOf U).index = Nat.card ↥U :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (R.subgroupOf U).index := fun hd =>
      hR.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
    have hrSub : r ∣ Nat.card ↥(R.subgroupOf U) :=
      ((Nat.Prime.dvd_mul hrprime).mp
        (by rw [hlag]; exact Nat.dvd_of_mem_primeFactors hr)).resolve_right hridx
    have hrR : r ∣ Nat.card ↥R := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRU).toEquiv] at hrSub
    intro h; rw [h, Subgroup.card_bot] at hrR
    exact hrprime.one_lt.ne' (Nat.eq_one_of_dvd_one hrR ▸ rfl)
  -- `N_G(R) < ⊤` (since `R ≤ M`, `R ≠ ⊥`, `G` simple), so it has a maximal overgroup `H`.
  have hNR_lt : Subgroup.normalizer (R : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG hM hRM hRne
  obtain ⟨H, hHcoatom, hNRH⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNR_lt.ne
  have hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hHcoatom, hNRH⟩
  obtain ⟨hF, hUMsH, hMH, hnorm, -⟩ :=
    typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  exact ⟨H, hH, hF, hUMsH, hMH, hnorm⟩

/-- **BG Lemma 14.13** (mmd L4059): extension of Theorem 14.4.  In the specified
multi-maximal sigma-length-one situation, `M` is Frobenius type, `tau_2(M)` is
empty, and `M` is a Frobenius group with kernel `M_sigma`.

⚠ **STATEMENT MIS-ENCODED (do not prove vacuously, 2026-06-30)**: the Coq original
(`non_disjoint_signalizer_Frobenius`, BGsection14:2412) hypothesises `1 < |𝓜_σ(x)|` and `M` *not*
a `σ(N[x])′`-group (`N[x]` = the signalizer neighbour).  The Lean hypotheses `M, N ∈ 𝓜_σ(x)` with
`¬ IsConjugateSubgroup M N` are **inconsistent**: by Theorem 13.9 non-conjugate maximals have
`σ(M) ∩ σ(N) = ∅`, but `x ∈ M_σ ∩ N_σ` with `x ≠ 1` forces a common prime — so the premise is
vacuous (the two elements of `𝓜_σ(x)` are conjugate, not non-conjugate).  A faithful restatement
replaces `{N, hN, hMN, hinter}` by `1 < (𝓜_σ(x)).ncard` and the `σ(N[x])′`-group condition.
Orphaned (no consumers); not on the FT path.  See issue 8020. -/
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

/-- **BG Corollary 14.10** (mmd L4008): global `σ`-length bound `ℓ_σ(g) ≤ 2`.

Assembled from the faithful `G#` cover.  The genuine `SigmaDecompositionData` is
`genuineSigmaDecomposition hG` (`length = sigmaLength`); `ℓ_σ(1) = 0` (`sigmaLength_eq_zero_iff`), and
for `g ≠ 1` the cover (`exists_mem_conjClassSet_Mtilde_or_fixed_zTilde` when a type-P maximal exists,
else `sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF`) places `g` in `𝒞_G(M̃)` or
`𝒞_G(Ẑ)`; conjugation-invariance (`sigmaLength_conj`) reduces to the per-piece bounds
`sigmaLength_le_two_of_mem_Mtilde` (sorry-free) and `sigmaLength_le_two_of_mem_zTilde_of_isTypeP`
(gated on the type-P partner-duality residual). -/
theorem exists_sigmaDecomposition_length_le_two [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ D : SigmaDecompositionData G, ∀ g : G, D.length g ≤ 2 := by
  refine ⟨genuineSigmaDecomposition hG, fun g => ?_⟩
  show sigmaLength g ≤ 2
  by_cases hg1 : g = 1
  · have h0 : sigmaLength g = 0 := (sigmaLength_eq_zero_iff hG g).mpr hg1
    omega
  · -- The `M̃`-piece closes by `sigmaLength_le_two_of_mem_Mtilde` after `sigmaLength_conj`.
    have hMtilde : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
        g ∈ conjClassSet (Mtilde hG (genuineSigmaDecomposition hG) M) → sigmaLength g ≤ 2 := by
      intro M hMmax hgM
      obtain ⟨m, hm, c, hcm⟩ := mem_conjClassSet.mp hgM
      rw [← hcm, sigmaLength_conj]
      exact sigmaLength_le_two_of_mem_Mtilde hG hMmax hm
    by_cases hP : (maximalTypePFamily G).Nonempty
    · obtain ⟨Mref, hMref, hMPref⟩ := hP
      obtain ⟨Kref, Kstarref, Uref, hKMref, hKref, hKstarref, hUref⟩ := exists_typeP_data hG hMref
      rcases exists_mem_conjClassSet_Mtilde_or_fixed_zTilde hG hMref hMPref hKMref hKref hKstarref
          hUref hg1 with ⟨M, hMmax, hgM⟩ | hgZ
      · exact hMtilde M hMmax hgM
      · obtain ⟨z, hz, c, hcz⟩ := mem_conjClassSet.mp hgZ
        rw [← hcz, sigmaLength_conj]
        exact sigmaLength_le_two_of_mem_zTilde_of_isTypeP hG hMref hMPref hKMref hKref hKstarref
          hUref hz
    · have htypeF : ∀ M : Subgroup G, M ∈ maximalSubgroups G → IsTypeF M := by
        intro M hM
        rw [isTypeF_iff_not_isTypeP]
        exact fun hMP => hP ⟨M, hM, hMP⟩
      have hgsharp : g ∈ sharpSubgroup (⊤ : Subgroup G) :=
        Set.mem_sdiff_singleton.mpr ⟨Subgroup.mem_top g, hg1⟩
      rw [sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF hG htypeF,
        Set.mem_iUnion₂] at hgsharp
      obtain ⟨M, hMmax, hgM⟩ := hgsharp
      exact hMtilde M hMmax hgM

/-! ### Subnormal closure into the `C(K)`-unique maximal (Coq `snK_sMst`)

Coq `P2type_signalizer` (BGsection14.v:2283) uses `snK_sMst L : K <|<| L → L ⊆ Mst`: any
subgroup `L` in which the `κ`-Hall `K` is *subnormal* is contained in the unique maximal `Mst`
over `C_G(K)`.  We port it here (S14 territory) via the base uniqueness `sK_uniqMst`
(`∀ a, K ≤ Mst^a → a ∈ Mst`) and a strong induction on `|L|` peeling normal layers
(`IsSubnormal.exists_normal_and_le_and_lt_top_of_ne`).  It supplies `E ⊆ Mst` (Coq `sDMst`)
for the signalizer decomposition Keystone C. -/

/-- **Coq `snK_sMst` single step**: if `N ⊆ Mstar`, `K ≤ N`, `L` normalizes `N`, and `K` has
the uniqueness property `∀ a, K ≤ Mstar^a → a ∈ Mstar` (Coq `sK_uniqMst`), then `L ⊆ Mstar`.
For `a ∈ L`, `a` normalizes `N`, so `N^{a⁻¹} = N`, whence `K^{a⁻¹} ≤ N^{a⁻¹} = N ⊆ Mstar`,
i.e. `K ≤ Mstar^a`, so `a ∈ Mstar`. -/
theorem le_partner_of_normalizes_of_le_of_uniq {K Mstar N L : Subgroup G}
    (hNMstar : N ≤ Mstar) (hKN : K ≤ N) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (huniq : ∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) :
    L ≤ Mstar := by
  intro a ha
  -- `a⁻¹` normalizes `N`, so `conj a⁻¹ • N = N`.
  have haN : MulAut.conj a⁻¹ • N = N :=
    OddOrder.GroupTheory.conj_smul_eq_self_of_mem_normalizer
      (Subgroup.inv_mem _ (hLN ha))
  -- `conj a⁻¹ • K ≤ conj a⁻¹ • N = N ≤ Mstar`.
  have hKconj : MulAut.conj a⁻¹ • K ≤ Mstar :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hKN).trans (haN.le.trans hNMstar)
  -- Rewrite as `K ≤ conj a • Mstar` and apply the uniqueness hypothesis.
  have hKMstar : K ≤ MulAut.conj a • Mstar := by
    have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a).mpr hKconj
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at this
  exact huniq a hKMstar

/-- **Coq `snK_sMst`** (BGsection14.v:2283): if `K` is *subnormal* in `L` (`K ≤ L`,
`(K.subgroupOf L).IsSubnormal`), `K ≤ Mstar`, and `K` has the uniqueness property
`∀ a, K ≤ Mstar^a → a ∈ Mstar`, then `L ⊆ Mstar`.  Strong induction on `|L|`: if `K = L`,
done; otherwise peel a proper `↥L`-normal overgroup `N̄` of `K.subgroupOf L`
(`exists_normal_and_le_and_lt_top_of_ne`), so `N := N̄.map L.subtype` is a proper subgroup with
`K ≤ N`, `K` subnormal in `N` (restriction), `L ≤ N_G(N)` (`N̄ ◁ ↥L`); the induction hypothesis
gives `N ⊆ Mstar`, and the single-step lemma lifts it to `L ⊆ Mstar`. -/
theorem le_partner_of_subnormal_of_uniq [Finite G] {K Mstar : Subgroup G}
    (huniq : ∀ a : G, K ≤ MulAut.conj a • Mstar → a ∈ Mstar) (hKMstar : K ≤ Mstar) :
    ∀ L : Subgroup G, K ≤ L → (K.subgroupOf L).IsSubnormal → L ≤ Mstar := by
  intro L
  induction hcard : Nat.card ↥L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    intro hKL hsub
    by_cases hKLtop : K.subgroupOf L = ⊤
    · -- `K = L` (as `K ≤ L`), so `L = K ≤ Mstar`.
      have hLK : L ≤ K := by
        intro x hx
        have hmem : (⟨x, hx⟩ : ↥L) ∈ K.subgroupOf L := by rw [hKLtop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).mp hmem
      exact hLK.trans hKMstar
    · -- Peel a proper `↥L`-normal overgroup `N̄` of `K.subgroupOf L`.
      obtain ⟨Nbar, hNbarnorm, hKNbar, hNbarlt⟩ :=
        hsub.exists_normal_and_le_and_lt_top_of_ne hKLtop
      haveI := hNbarnorm
      set N : Subgroup G := Nbar.map L.subtype with hNdef
      have hNL : N ≤ L := Subgroup.map_subtype_le _
      have hNbar_eq : N.subgroupOf L = Nbar :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective Nbar
      -- `K ≤ N`.
      have hKN : K ≤ N := by
        have hmm : (K.subgroupOf L).map L.subtype ≤ N := Subgroup.map_mono hKNbar
        rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL] at hmm
      -- `|N| < |L|` (proper).
      have hNlt : Nat.card ↥N < Nat.card ↥L := by
        have hNbne : N ≠ L := by
          intro h
          apply hNbarlt.ne
          rw [← hNbar_eq, h, Subgroup.subgroupOf_self]
        refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hNL))
          (fun heq => hNbne (Subgroup.eq_of_le_of_card_ge hNL heq.ge))
      -- `K` subnormal in `N` (restrict the subnormal series along `N ≤ L`).
      have hKNsub : (K.subgroupOf N).IsSubnormal := by
        have hcomap := hsub.comap (Subgroup.inclusion hNL)
        rwa [Subgroup.comap_inclusion_subgroupOf hNL] at hcomap
      -- Induction hypothesis: `N ⊆ Mstar`.
      have hNMstar : N ≤ Mstar := ih (Nat.card ↥N) (hcard ▸ hNlt) N rfl hKN hKNsub
      -- `L ≤ N_G(N)` (`N̄ ◁ ↥L`), so the single-step lemma gives `L ⊆ Mstar`.
      have hLnN : L ≤ Subgroup.normalizer (N : Set G) := by
        rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hNL, hNbar_eq]
        exact hNbarnorm
      exact le_partner_of_normalizes_of_le_of_uniq hNMstar hKN hLnN huniq

/-! ### Subnormality in nilpotent groups (mathcomp `nilpotent_subnormal`)

Two general group-theory facts used to feed `le_partner_of_subnormal_of_uniq` in the signalizer
decomposition below (Coq `nilpotent_subnormal (Fitting_nil D) sK_FD`).  Not `S14`-specific. -/

/-- **Every subgroup of a finite nilpotent group is subnormal** (mathcomp `nilpotent_subnormal`).
Strong induction on the index: for `H ≠ ⊤` the normalizer condition
(`Group.normalizerCondition_of_isNilpotent`) gives `H < N(H)`, `H ⊴ N(H)` (`normal_in_normalizer`), and
`[Γ : N(H)] < [Γ : H]` (`index_strictAnti`), so the IH makes `N(H)` subnormal;
then `IsSubnormal.step`. -/
theorem isSubnormal_of_isNilpotent {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (H : Subgroup Γ) : H.IsSubnormal := by
  have hnc : NormalizerCondition Γ := Group.normalizerCondition_of_isNilpotent
  induction hidx : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHtop : H = ⊤
    · exact hHtop ▸ Subgroup.IsSubnormal.top
    · have hlt : H < Subgroup.normalizer (H : Set Γ) := hnc H (lt_top_iff_ne_top.mpr hHtop)
      have hidxlt : (Subgroup.normalizer (H : Set Γ)).index < n := by
        rw [← hidx]; exact Subgroup.index_strictAnti hlt
      have hstep : (Subgroup.normalizer (H : Set Γ)).IsSubnormal :=
        ih _ hidxlt (Subgroup.normalizer (H : Set Γ)) rfl
      exact Subgroup.IsSubnormal.step H (Subgroup.normalizer (H : Set Γ)) hlt.le hstep
        Subgroup.normal_in_normalizer

/-- **A subgroup contained in a normal, nilpotent subgroup is subnormal** in the ambient group
(mathcomp `nilpotent_subnormal` + `normal_subnormal` + transitivity): `H ≤ N ⊴ Γ` with `N` nilpotent
gives `H.subgroupOf N` subnormal in `↥N` (previous lemma), `N` subnormal in `Γ`
(`Normal.isSubnormal`), so `IsSubnormal.trans`. -/
theorem isSubnormal_of_le_normal_nilpotent {Γ : Type*} [Group Γ] [Finite Γ] {H N : Subgroup Γ}
    (hHN : H ≤ N) (hNnorm : N.Normal) (hNnil : Group.IsNilpotent ↥N) : H.IsSubnormal := by
  haveI := hNnil
  exact Subgroup.IsSubnormal.trans hHN (isSubnormal_of_isNilpotent (H.subgroupOf N))
    hNnorm.isSubnormal

/-- **Signalizer σ-decomposition `H_σ ⊔ (H ∩ M*) = H` for BG Theorem 15.8** (Coq
`tau2_P2type_signalizer`, `set D := H :&: L` + `sdprod_sigma maxH hallD`, BGsection15.v:1273/1374,
resting on `P2type_signalizer`, BGsection14.v:2283/2374): for the Corollary 14.12 signalizer
neighbour `H` of the type-`P₂` maximal `M` (with `M* ∈ 𝓜(C_G(K))`, `H ∈ 𝓜(N_G(R))`), the
`E`-setup complement `E` of `H_σ` (which contains `K` with `K ⊆ F(E)`, from
`typeP2_neighbor_is_typeF_of_mem`) lies in `M*`, so `H_σ ⊔ (H ∩ M*) ⊇ H_σ ⊔ E = H`.

**Proof (weaker than Coq's exact `H ∩ M* = D`).**  Coq proves the exact identity `H ∩ M* = D` (its
σ(H)′-Hall) via the harder `H_σ ∩ M* = 1` step, needed for its Hall/Fitting clauses.  The repo goal
is only the *join* `H_σ ⊔ (H ∩ M*) = H`, so the easy inclusion `E ⊆ H ∩ M*` suffices.  `E ⊆ M*`
comes from `le_partner_of_subnormal_of_uniq` (Coq `snK_sMst`): `K` is subnormal in `E`
(`K ⊆ F(E)`, `F(E)` normal nilpotent, `isSubnormal_of_le_normal_nilpotent`), `K ⊆ M*`
(`K ⊆ M*_σ`), and the uniqueness `K ≤ M*^a → a ∈ M*` (Coq `sK_uniqMst`, `partner_inf_and_uniq`);
`M* = Mst` (the dual partner) since `𝓜(C(K)) = {Mst}` (Prop 14.2(d)).  (issue 9017 更新 #12/#13.) -/
theorem signalizer_msigma_sup_inf_partner_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Mstar U K R H : Subgroup G} {r : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)))
    (hr : r ∈ piSet U) (hRU : R ≤ U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hH : H ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G))) :
    OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mstar) = H := by
  classical
  have hP : IsTypeP M := hP2.1
  -- Dual partner `Mst` (Theorem 14.7 / `typeP_duality`).
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨Mst, hMstprop, hMstuniq⟩ := (typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, hMnc, hMstpair, hZcyc, hZti, hP2or, hcover⟩ := hMstprop
  -- Uniqueness `sK_uniqMst : K ≤ Mst^a → a ∈ Mst` (Coq), and `K ≤ M*_σ` (⟹ `K ≤ Mst`).
  have hKMsigmaMst : K ≤ OddOrder.BG.Ch3.S10.Msigma Mst :=
    (le_of_eq hMstpair.2.2).trans inf_le_left
  have hMsMst : OddOrder.BG.Ch3.S10.Msigma M ⊓ Mst = Kstar :=
    msigma_inf_partner_eq_kstar hG hM hP2 hKM hKstardef hMstmax hKMsigmaMst hMstpair.1 hMnc
  have hKstarM : Kstar ≤ M := by
    rw [hKstardef]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  have hKstarNe : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstardef hU).2.1
  have hKNe : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨hziMMst, hsKuniq⟩ := partner_inf_and_uniq hG hMstmax hMstP hMstpair.1 hMstpair.2.1
    hMstpair.2.2 hKMsigmaMst hKM hKstarM hZcyc hKstarNe hKNe hMsMst
  -- `𝓜(C(K)) = {Mst}` (Prop 14.2(d) for `Mst`), so `Mstar = Mst`.
  obtain ⟨-, -, -, -, hP2struct, -, -⟩ := typeP_structure hG hM hP hKM hK hKstardef hU
  obtain ⟨-, q, hqprime, hKcard, -⟩ := hP2struct hP2
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard,
      by rw [hKcard, pow_one]⟩
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    haveI hMstsol : IsSolvable ↥Mst := hG.solvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  have hMstarEq : Mstar = Mst := by
    have hmem := hMstar; rw [huniqMst] at hmem; exact Set.mem_singleton_iff.mp hmem
  rw [hMstarEq]
  -- `E`-setup from the neighbour lemma: `M_σ(H) ⊔ E = H`, `K ≤ E`, `K ≤ F(E)`.
  obtain ⟨-, -, -, -, E, E₁, E₂, E₃, hEsetup, hKE, hKFE⟩ :=
    typeP2_neighbor_is_typeF_of_mem hG hM hP2 hKM hUM hK hU hUab hr hRU hR hKNU hH
  -- `E ≤ Mst` via subnormal closure (Coq `snK_sMst`): `K ⊴⊴ E`, `K ≤ Mst`, uniqueness.
  have hKMst : K ≤ Mst := hKMsigmaMst.trans (OddOrder.BG.Ch3.S10.Msigma_le Mst)
  have hKsubnormal : (K.subgroupOf E).IsSubnormal := by
    haveI : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
      OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E
    refine isSubnormal_of_le_normal_nilpotent
      (N := (OddOrder.BG.Ch2.S08.fittingInG E).subgroupOf E) ?_
      (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal E)
      (Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch2.S08.fittingInG_le E)).symm)
    exact Subgroup.comap_mono hKFE
  have hEMst : E ≤ Mst := le_partner_of_subnormal_of_uniq hsKuniq hKMst E hKE hKsubnormal
  -- Conclude: `E ⊆ H ∩ Mst` and `M_σ(H) ⊔ E = H`.
  refine le_antisymm (sup_le (OddOrder.BG.Ch3.S10.Msigma_le H) inf_le_left) ?_
  calc H = OddOrder.BG.Ch3.S10.Msigma H ⊔ E := hEsetup.E_compl_sup.symm
    _ ≤ OddOrder.BG.Ch3.S10.Msigma H ⊔ (H ⊓ Mst) :=
        sup_le_sup_left (le_inf hEsetup.E_le hEMst) _

end OddOrder.BG.Ch4.S14

