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
import OddOrder.BG.Ch1_Preliminary.S03c_Thm37
import OddOrder.BG.Ch1_Preliminary.S03g_Thm310
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
    push_neg at hcon
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
  simp only [maximalTypeFFamily, maximalTypePFamily, Set.mem_setOf_eq, Set.mem_diff, not_and]
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
  simp only [sigmaSharp, sharpSubgroup, Set.mem_diff, Set.mem_singleton_iff,
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
            ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G))) := by
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
      push_neg at hcon
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
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
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
    refine ⟨hKprime, ?_, ?_, ?_, ?_⟩
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
  sorry

/-! ## Theorem 14.4 and Lemma 14.5: sigma-length one centralizers -/

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
            tau2 N ⊆ OddOrder.BG.Ch3.S10.sigma M ∧
            OddOrder.BG.Ch3.S10.sigma N ∩ piSet M ⊆ OddOrder.BG.Ch3.S10.beta N ∧
            Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
              ((M ⊓ N).subgroupOf N)) := by
  sorry

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
    Set.mem_diff, Set.mem_singleton_iff, SetLike.mem_coe] at hgM hgN
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

/-! ## Theorem 14.7 through Lemma 14.13: type-P duality and global counting -/

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
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) ∧
    Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M)) (Nat.card ↥(K.subgroupOf M)) ∧
    ∃! Mstar : Subgroup G,
      Mstar ∈ maximalSubgroups G ∧ IsTypeP Mstar ∧ ¬ IsConjugateSubgroup M Mstar ∧
      Ch03.IsHallSubgroup (kappa Mstar) (Kstar.subgroupOf Mstar) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ IsTISubset (zTilde K Kstar) (K ⊔ Kstar) ∧
      (IsTypeP2 M ∨ IsTypeP2 Mstar) ∧
      (∀ H : Subgroup G, H ∈ maximalSubgroups G → IsTypeP H →
        IsConjugateSubgroup H M ∨ IsConjugateSubgroup H Mstar) := by
  sorry

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
  sorry

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

/-- **BG Corollary 14.10** (mmd L4008): global sigma-length bound. -/
theorem exists_sigmaDecomposition_length_le_two [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ D : SigmaDecompositionData G, ∀ g : G, D.length g ≤ 2 := by
  sorry

/-- **BG Lemma 14.11** (mmd L4086): for `M ∈ 𝓜_F` with `E` a complement of `M_σ` in `M`, a
prime `q ∈ π(E)`, and `Q ∈ ℰ_q¹(E)` with `Q ⊄ F(E)`, there is `M* ∈ 𝓜` with either
(1) `q ∈ τ₂(M*)` and `𝓜(C_G(Q)) = {M*}`, or (2) `q ∈ κ(M*)` and `M* ∈ 𝓜_{P₁}`.

"Of independent interest" (BG L4084); used here only by Corollary 14.12.  `F(E)` is the Fitting
subgroup of the complement `E`, taken in `G` via `fittingInG`.  Gated on §13. -/
theorem exists_maximal_of_typeF_notMem_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E Q : Subgroup G} {q : ℕ} (hM : M ∈ maximalSubgroups G) (hF : IsTypeF M)
    (hE : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))
    (hq : q ∈ piSet E) (hQ : Q ∈ elemAbelianOfRank G q 1) (hQE : Q ≤ E)
    (hQF : ¬ Q ≤ OddOrder.BG.Ch2.S08.fittingInG E) :
    ∃ Mstar : Subgroup G, Mstar ∈ maximalSubgroups G ∧
      ((q ∈ tau2 Mstar ∧
          maximalSubgroupsContaining (Subgroup.centralizer (Q : Set G)) = {Mstar}) ∨
       (q ∈ kappa Mstar ∧ IsTypeP1 Mstar)) := by
  sorry

/-- **BG Corollary 14.12** (mmd L4035): for `M ∈ 𝓜_{P₂}` with `K`, `M*`, `K*` as in
Theorem 14.7 and `U` as in Proposition 14.2(a), `r ∈ π(U)`, `R` the Sylow `r`-subgroup of the
abelian `U`, and `H ∈ 𝓜(N_G(R))`: then `H ∈ 𝓜_F`, `U ⊆ H_σ`, `M ∩ H = U K`, `N_H(U) ⊄ M`,
`K ⊆ F(H ∩ M*)`, and `H ∩ M*` complements `H_σ` in `H`.

**Faithfulness (2026-06-15):** the hypotheses are now tightened to BG — `U` is the specific
abelian Hall `(κ(M) ∪ σ(M))'`-factor of Proposition 14.2(a) and `R` is a *Sylow* `r`-subgroup
of `U` (`IsHallSubgroup {r}`), not an arbitrary `U ≤ M`, `R ≤ U` with `R ≠ ⊥` (under which the
conclusion fails).  The conclusion is a faithful partial: it captures `H ∈ 𝓜_F`, `U ⊆ H_σ`,
and `M ∩ H = U ⊔ K`, and defers `N_H(U) ⊄ M`, `K ⊆ F(H ∩ M*)`, the complement clause, and the
dual-pair data (gated on §13).  See `notes/bg/s14_typeP_counting.md`. -/
theorem typeP2_neighbor_is_typeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U R : Subgroup G} {r : ℕ} (hM : M ∈ maximalSubgroups G) (hP2 : IsTypeP2 M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hr : r ∈ piSet U)
    (hR : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U)) :
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

