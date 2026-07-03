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

/-- `β` is conjugation-invariant: `β(M^g) = β(M)`.  `α` transports along the conjugation
isomorphism (`Nat.card` and `pRank` invariance), and `idealPrime` is a `G`-global condition. -/
theorem beta_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.beta (MulAut.conj g • M) = OddOrder.BG.Ch3.S10.beta M := by
  have e := conjSubgroupEquiv g M
  ext p
  simp only [OddOrder.BG.Ch3.S10.mem_beta_iff, OddOrder.BG.Ch3.S10.mem_alpha_iff]
  rw [Nat.card_congr e.toEquiv, OddOrder.BG.Ch3.S13.pRank_eq_of_mulEquiv (p := p) e]

/-! ## The Frobenius consequence of type `F` with no `τ₂`-primes -/

/-- **Type `F` with no `τ₂`-primes is Frobenius over `M_σ`** (the `∃ U` conclusion of BG
Lemma 14.13(a)): if `κ(M) = ∅`, no prime lies in `τ₂(M)`, and some prime of `π(M)` is
outside `σ(M)` (so the complement is nontrivial), then `M = M_σ ⋊ E` is a Frobenius group.

A fixed point `n ∈ M_σ^#` of `e ∈ E^#` would give a prime `r` of `orderOf e` — necessarily
in `τ₁(M) ∪ τ₃(M)` by the `π(E)`-partition (Lemma 12.1) and `τ₂`-freeness — a rank-one
subgroup `X ≤ ⟨e⟩` with `C_{M_σ}(X) ≠ 1`, i.e. `r ∈ κ(M)` — contradiction. -/
theorem typeF_frobenius_of_tau2_prime_free [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M)
    (ht2 : ∀ p : ℕ, p.Prime → p ∉ tau2 M)
    {q : ℕ} (hqπ : q ∈ S14.piSet M) (hqσ : q ∉ OddOrder.BG.Ch3.S10.sigma M) :
    ∃ U : Subgroup G,
      Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        (U.subgroupOf M) ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (U.subgroupOf M) := by
  classical
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
  have hcompl : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).IsComplement'
      (E.subgroupOf M) := hsetup.isComplement'_subgroupOf
  -- `q ∣ |E|`: `q ∈ π(M) ∖ σ(M)` and `M_σ` is the `σ`-Hall of `M`.
  have hMσhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
  have hcardE : Nat.card ↥(E.subgroupOf M) =
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := (hcompl.symm.index_eq_card).symm
  have hqE : q ∣ Nat.card ↥(E.subgroupOf M) := by
    rw [hcardE]
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqπ
    -- `q ∣ |M| = |M_σ| ⬝ [M : M_σ]` and `q ∤ |M_σ|` (a `σ`-group).
    have hdvdM : q ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hqπ).2.1
    have hprod : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) *
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    rcases (Nat.Prime.dvd_mul hq_prime).mp (hprod ▸ hdvdM) with h | h
    · exact absurd (hMσhall.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, h, Nat.card_pos.ne'⟩)) hqσ
    · exact h
  have hEne : E.subgroupOf M ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, Nat.dvd_one] at hqE
    exact (Nat.prime_of_mem_primeFactors hqπ).one_lt.ne' hqE
  -- `π(E) ⊆ σ(M)ᶜ` (the complement realizes the `σ'`-index).
  have hEpi : ∀ r ∈ (Nat.card ↥(E.subgroupOf M)).primeFactors,
      r ∉ OddOrder.BG.Ch3.S10.sigma M := by
    intro r hr
    rw [hcardE] at hr
    exact hMσhall.2 r hr
  refine ⟨E, hcompl, ?_⟩
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
    · -- Type `P₁`: `q ∈ κ(M)`; the dual pair forces `p` into a rank-one position.
      sorry
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
    sorry
  -- ### Part 3: the Frobenius conclusion
  exact ⟨hFM, ht2M,
    typeF_frobenius_of_tau2_prime_free hG hM hFM ht2M hqπM hqσM⟩

end OddOrder.BG.Ch4.S16
