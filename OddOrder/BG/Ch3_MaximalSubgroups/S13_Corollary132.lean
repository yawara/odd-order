/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Lemma131
import OddOrder.BG.Ch3_MaximalSubgroups.S12_ExceptionalBridge

/-!
# BG §13: Corollary 13.2 (`τ₁(M) ∪ τ₃(M)`-specialization of Lemma 13.1)

**スコープ**: Bender–Glauberman §13, mmd `references/bg/local-analysis.mmd` L3548-3554.

`p ∈ τ₁(M) ∪ τ₃(M)`, `P` を `M` の非自明 `p`-部分群、`M* ∈ ℳ(N_G(P))` とすると
(a) `M ∩ M*` の全 `p`-部分群が `M_σ ∩ M*` を中心化;
(b) `E ∩ M*` の全 `τ₁(M*)'`-部分群が `M_σ ∩ M*` を中心化;
(c) `[M_σ ∩ M*, M ∩ M*] ≠ 1` なら `p ∈ σ(M*)`、かつ `p ∈ τ₁(M)` なら `p ∈ β(M*)`。

**証明** (mmd L3554): Lemma 12.2(a) で `p ∈ σ(M*) ∪ τ₂(M*)`、`p ∈ τ₁(M)∪τ₃(M)` ゆえ `M*` は `M` と
非共役 (Lemma 12.2(b) = `not_conj_of_mem_tau1_union_tau3_of_normalizer_le`)。あとは Lemma 13.1
((a)=`pSubgroup_centralizes_Msigma_inf`, (b)=`not_mem_tau2_of_interaction`,
(c)=`mem_idealPrime_of_tau1_of_interaction`) から従う。`[M_σ∩M*, M∩M*] = 1` の場合は直接中心化。

(b) は per-prime: `τ₁(M*)'`-部分群 `Q` の各素冪部分群に Lemma 13.1(a) を適用し、
`le_centralizer_of_forall_prime_isPGroup`(有限群は素冪部分群で生成される)で組み立てる。

(c) の `β(M*)` 部分は `p ∈ σ(M*)` から `r_p(M*) = r_p(G)`
(`pRank_eq_of_mem_sigma`)、`idealPrime` の `r_p(G) ≥ 3` と合わせて `p ∈ α(M*)`。
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Reusable helpers -/

/-- **A finite group is "centralized" once all its prime-power subgroups are.** If every
prime-power subgroup `R ≤ K` lies in `C_G(C)`, then `K ≤ C_G(C)`. Proof: for `y ∈ K`, split
`y = w * z` (Bézout) into commuting `r`-part `z` and `r'`-part `w` of strictly smaller order, and
induct on `orderOf y`. The `r`-part is a prime-power subgroup (apply the hypothesis); the `r'`-part
falls to the induction hypothesis. Reusable for any "`π'`-subgroup centralizes" argument. -/
theorem le_centralizer_of_forall_prime_isPGroup [Finite G] {K C : Subgroup G}
    (h : ∀ r : ℕ, r.Prime → ∀ R : Subgroup G, R ≤ K → IsPGroup r ↥R →
      R ≤ Subgroup.centralizer (C : Set G)) :
    K ≤ Subgroup.centralizer (C : Set G) := by
  -- It suffices to prove, by strong induction on `n = orderOf y`, that every `y ∈ K` with
  -- `orderOf y = n` centralizes `C`.
  suffices H : ∀ n : ℕ, ∀ y : G, y ∈ K → orderOf y = n →
      y ∈ Subgroup.centralizer (C : Set G) by
    intro y hy
    exact H (orderOf y) y hy rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro y hyK hyord
    rcases eq_or_ne n 1 with hn1 | hn1
    · -- `orderOf y = 1 ⟹ y = 1`.
      have hy1 : y = 1 := orderOf_eq_one_iff.mp (by rw [hyord, hn1])
      rw [hy1]; exact Subgroup.one_mem _
    · have hn0 : n ≠ 0 := by rw [← hyord]; exact (orderOf_pos y).ne'
      -- pick a prime `r ∣ n`.
      obtain ⟨r, hr, hrdvd⟩ := n.exists_prime_and_dvd hn1
      haveI : Fact r.Prime := ⟨hr⟩
      set ra : ℕ := ordProj[r] n with hra
      set m : ℕ := ordCompl[r] n with hmdef
      have hsplit : ra * m = n := Nat.ordProj_mul_ordCompl_eq_self n r
      have hmdvd : m ∣ n := Nat.ordCompl_dvd n r
      have hradvd : ra ∣ n := Nat.ordProj_dvd n r
      have hapos : 0 < n.factorization r := hr.factorization_pos_of_dvd hn0 hrdvd
      have hra2 : 2 ≤ ra := by
        calc 2 ≤ r := hr.two_le
        _ = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ n.factorization r := Nat.pow_le_pow_right hr.pos hapos
      have hm0 : m ≠ 0 := by
        intro h0; apply hn0; rw [← hsplit, h0, mul_zero]
      have hra0 : ra ≠ 0 := by
        intro h0; apply hn0; rw [← hsplit, h0, zero_mul]
      -- `z = y ^ m` is the `r`-part: `orderOf z = ra = r ^ a`.
      set z : G := y ^ m with hz
      have hzord : orderOf z = ra := by
        rw [hz, orderOf_pow' y hm0, hyord, Nat.gcd_eq_right hmdvd]
        exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm0) hsplit.symm
      have hzpg : IsPGroup r ↥(Subgroup.zpowers z) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hzord, hra])
      have hzK : (Subgroup.zpowers z : Subgroup G) ≤ K := by
        rw [Subgroup.zpowers_le]; exact hz ▸ K.pow_mem hyK m
      have hzC : z ∈ Subgroup.centralizer (C : Set G) :=
        h r hr _ hzK hzpg (Subgroup.mem_zpowers z)
      -- `w = y ^ ra` is the `r'`-part: `orderOf w = m < n`, induction applies.
      set w : G := y ^ ra with hw
      have hword : orderOf w = m := by
        rw [hw, orderOf_pow' y hra0, hyord, Nat.gcd_eq_right hradvd]
      have hmlt : m < n := by
        have : 2 * m ≤ ra * m := Nat.mul_le_mul_right m hra2
        rw [hsplit] at this
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        omega
      have hwK : w ∈ K := hw ▸ K.pow_mem hyK ra
      have hwC : w ∈ Subgroup.centralizer (C : Set G) := IH m hmlt w hwK hword
      -- Bézout: `ra` and `m` are coprime, so `1 = ra * A + m * B` and `y = w ^ A * z ^ B`.
      have hcop : Nat.Coprime ra m := (Nat.coprime_ordCompl hr hn0).pow_left _
      have hbez : (ra : ℤ) * Nat.gcdA ra m + (m : ℤ) * Nat.gcdB ra m = 1 := by
        have hg := Nat.gcd_eq_gcd_ab ra m
        rw [hcop, Nat.cast_one] at hg
        linarith [hg]
      have hyeq : y = w ^ Nat.gcdA ra m * z ^ Nat.gcdB ra m := by
        have : y ^ (1 : ℤ) = w ^ Nat.gcdA ra m * z ^ Nat.gcdB ra m := by
          rw [← hbez, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hw, ← hz]
        rwa [zpow_one] at this
      rw [hyeq]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hwC _) (Subgroup.zpow_mem _ hzC _)

/-- **Order argument**: if `C ≤ H` (finite) and for every prime `q` some subgroup `S ≤ C` has
the full `q`-part of `|H|` as its order (`|S| = q ^ v_q(|H|)`, i.e. `S` is a Sylow `q` of `H`
lying in `C`), then `C = H`. The `S` witness that `|C|` carries the full `q`-part of `|H|` for
every `q`, so `|H| ∣ |C|`, and `C ≤ H` gives `|C| ∣ |H|`, hence equality. Reusable for
coprime-action "invariant Sylows generate" arguments. -/
theorem eq_of_le_of_forall_full_prime_pow [Finite G] {H C : Subgroup G} (hCH : C ≤ H)
    (hS : ∀ q : ℕ, q.Prime → ∃ S : Subgroup G, S ≤ C ∧
      Nat.card ↥S = q ^ (Nat.card ↥H).factorization q) : C = H := by
  have hdvd : Nat.card ↥H ∣ Nat.card ↥C := by
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    intro q
    by_cases hq : q.Prime
    · haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨S, hSC, hScard⟩ := hS q hq
      have hpow : q ^ (Nat.card ↥H).factorization q ∣ Nat.card ↥C :=
        hScard ▸ Subgroup.card_dvd_of_le hSC
      exact (Nat.Prime.pow_dvd_iff_le_factorization hq Nat.card_pos.ne').mp hpow
    · rw [Nat.factorization_eq_zero_of_non_prime _ hq]; exact Nat.zero_le _
  have heq : Nat.card ↥C = Nat.card ↥H :=
    Nat.dvd_antisymm (Subgroup.card_dvd_of_le hCH) hdvd
  have hsub : C.subgroupOf H = ⊤ :=
    Subgroup.eq_top_of_card_eq _
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv, heq])
  exact le_antisymm hCH (Subgroup.subgroupOf_eq_top.mp hsub)

/-- **Coprime `A`-invariant Sylow existence (subgroup form)**: if `A ≤ N_G(N)`, `|A|` and `|N|`
are coprime, and `A` or `N` is solvable, then for every prime `q`, `N` has an `A`-invariant
Sylow `q`-subgroup `S` (`S ≤ N`, `IsPGroup q S`, `A ≤ N_G(S)`, `|S| = q ^ v_q(|N|)`).
Encapsulates the `MulDistribMulAction`/`φ`-action boilerplate around
`Isaacs.Ch04.exists_aInvariant_sylow` (Isaacs Thm 3.23(a)); reusable for §13 coprime arguments. -/
theorem exists_aInvariant_sylow_subgroup [Finite G] {A N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N))
    (hSolv : IsSolvable ↥A ∨ IsSolvable ↥N) (q : ℕ) [Fact q.Prime] :
    ∃ S : Subgroup G, S ≤ N ∧ IsPGroup q ↥S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
      Nat.card ↥S = q ^ (Nat.card ↥N).factorization q := by
  classical
  letI act : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hAN)
  set φ : ↥A →* MulAut ↥N := MulDistribMulAction.toMulAut ↥A ↥N with hφ
  have hφ_coe : ∀ (a : ↥A) (x : ↥N), (N.subtype ((φ a) x)) = (↑a) * (N.subtype x) * (↑a)⁻¹ :=
    fun _ _ => rfl
  have hφ_inv_coe : ∀ (a : ↥A) (x : ↥N),
      (N.subtype (((φ a)⁻¹) x)) = (↑a)⁻¹ * (N.subtype x) * (↑a) := by
    intro a x; rw [← map_inv]; simpa using hφ_coe a⁻¹ x
  obtain ⟨S', hS'inv⟩ := OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (φ := φ) hcop hSolv q
  set S : Subgroup G := (S' : Subgroup ↥N).map N.subtype with hSdef
  refine ⟨S, Subgroup.map_subtype_le _,
    S'.2.of_equiv (Subgroup.equivMapOfInjective _ _ N.subtype_injective), ?_, ?_⟩
  · intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hxS, rfl⟩
      exact ⟨(φ ⟨a, ha⟩) x, hS'inv.smul_mem ⟨a, ha⟩ hxS, hφ_coe ⟨a, ha⟩ x⟩
    · rintro ⟨x, hxS, hx⟩
      refine ⟨((φ ⟨a, ha⟩)⁻¹) x, hS'inv.inv_smul_mem ⟨a, ha⟩ hxS, ?_⟩
      rw [hφ_inv_coe ⟨a, ha⟩ x, hx]
      change a⁻¹ * (a * y * a⁻¹) * a = y
      group
  · rw [hSdef, Subgroup.card_map_of_injective N.subtype_injective, S'.card_eq_multiplicity]

/-- A nonidentity `r`-subgroup `R` of `H` forces `r ∈ π(H)`. -/
theorem mem_primeFactors_of_isPGroup_le [Finite G] {r : ℕ} (hr : r.Prime)
    {R H : Subgroup G} (hRH : R ≤ H) (hRne : R ≠ ⊥) (hRr : IsPGroup r ↥R) :
    r ∈ (Nat.card ↥H).primeFactors := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := hRr.exists_card_eq
  have hRcard1 : Nat.card ↥R ≠ 1 := fun hh => hRne (Subgroup.card_eq_one.mp hh)
  have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; exact hRcard1 hk
  have hrdvdH : r ∣ Nat.card ↥H :=
    dvd_trans (hk ▸ dvd_pow_self r hk0) (Subgroup.card_dvd_of_le hRH)
  exact Nat.mem_primeFactors.mpr ⟨hr, hrdvdH, Nat.card_pos.ne'⟩

/-- If `p ∈ π(M)` but `p ∉ σ(M)`, then `p ∈ π(E)` (`|M| = |M_σ| · |E|` and `π(M_σ) ⊆ σ(M)`). -/
theorem mem_primeFactors_E_of_mem_M_of_not_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} (hp : p.Prime)
    (hpM : p ∈ (Nat.card ↥M).primeFactors) (hpσ : p ∉ S10.sigma M) :
    p ∈ (Nat.card ↥E).primeFactors := by
  have hdvdM : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpM).2.1
  rw [← h.card_Msigma_mul_card_E] at hdvdM
  rcases (Nat.Prime.dvd_mul hp).mp hdvdM with hdvdMsig | hdvdE
  · exact absurd (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨hp, hdvdMsig, Nat.card_pos.ne'⟩)) hpσ
  · exact Nat.mem_primeFactors.mpr ⟨hp, hdvdE, Nat.card_pos.ne'⟩

/-- For `p ∈ σ(M)`, the Sylow `p`-subgroup of `M` is a Sylow `p`-subgroup of `G`, so
`r_p(M) = r_p(G)`. -/
theorem pRank_eq_of_mem_sigma [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p ∈ S10.sigma M) : pRank ↥M p = pRank G p := by
  obtain ⟨P⟩ : Nonempty (Sylow p ↥M) := inferInstance
  obtain ⟨S, hS⟩ := S10.isSylow_sylowMap_of_mem_sigma hp P
  rw [← pRank_sylow_eq P, ← pRank_sylow_eq S, hS]
  exact pRank_eq_of_mulEquiv
    (Subgroup.equivMapOfInjective (P : Subgroup ↥M) M.subtype M.subtype_injective)

/-! ## Corollary 13.2 -/

/-- **BG Corollary 13.2** (mmd L3548): `p ∈ τ₁(M)∪τ₃(M)`, `P` 非自明 `p`-部分群 of `M`,
`M* ∈ ℳ(N_G(P))` なら (a) `M∩M*` の全 `p`-部分群が `M_σ∩M*` を中心化; (b) `E∩M*` の全
`τ₁(M*)'`-部分群が `M_σ∩M*` を中心化; (c) `[M_σ∩M*,M∩M*]≠1` なら `p ∈ σ(M*)`、かつ
`p ∈ τ₁(M)` なら `p ∈ β(M*)`。

**証明** (mmd L3554): `[M_σ∩M*, M∩M*] = 1` の場合は `M∩M*` がそのまま `M_σ∩M*` を中心化。
`≠ 1` の場合、Lemma 12.2(b) で `M*` が `M` と非共役、Lemma 12.2(a) で `p ∈ σ(M*)∪τ₂(M*)`。
あとは Lemma 13.1 (b)(c) で `p ∉ τ₂(M*)`・`p ∈ β(G)`、(a) で各 `p`-部分群の中心化を得る。
(b) は `τ₁(M*)'`-部分群 `Q` の各素冪部分群に (a) を適用し
`le_centralizer_of_forall_prime_isPGroup` で組み立てる。 -/
theorem tau13_pSubgroup_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1 M ∪ tau3 M) {P : Subgroup G} (hPM : P ≤ M) (hPne : P ≠ ⊥) (hPp : IsPGroup p ↥P)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G))) :
    (∀ Q : Subgroup G, Q ≤ M ⊓ Mstar → IsPGroup p ↥Q →
      Q ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G)) ∧
    (∀ Q : Subgroup G, Q ≤ E ⊓ Mstar → Subgroup.IsPiSubgroup ((tau1 Mstar)ᶜ) Q →
      Q ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G)) ∧
    (⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ →
      p ∈ S10.sigma Mstar ∧ (p ∈ tau1 M → p ∈ S10.beta Mstar)) := by
  classical
  -- common setup
  have hMmax : M ∈ maximalSubgroups G := h.mem_maximal
  obtain ⟨hMstarCo, hN⟩ := mem_maximalSubgroupsContaining.mp hMstar
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  have hPMstar : P ≤ Mstar := le_trans Subgroup.le_normalizer hN
  have hEle : E ≤ M := h.E_le
  have hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar :=
    not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG hMmax hp hPM hPne hPp hN
  have hpσM : p ∉ S10.sigma M := by
    rcases hp with h1 | h3
    · exact tau1_subset_sigma_compl M h1
    · exact tau3_subset_sigma_compl M h3
  have hpπM : p ∈ (Nat.card ↥M).primeFactors :=
    mem_primeFactors_of_isPGroup_le Fact.out hPM hPne hPp
  have hpπMstar : p ∈ (Nat.card ↥Mstar).primeFactors :=
    mem_primeFactors_of_isPGroup_le Fact.out hPMstar hPne hPp
  have hpπE : p ∈ (Nat.card ↥E).primeFactors :=
    mem_primeFactors_E_of_mem_M_of_not_sigma hG h Fact.out hpπM hpσM
  by_cases hcomm : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ = ⊥
  · -- `[M_σ∩M*, M∩M*] = 1`: every subgroup of `M∩M*` centralizes `M_σ∩M*`.
    have hcent : (M ⊓ Mstar : Subgroup G) ≤
        Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Subgroup.commutator_comm (S10.Msigma M ⊓ Mstar) (M ⊓ Mstar) ▸ hcomm)
    refine ⟨fun Q hQ _ => hQ.trans hcent, fun Q hQ _ => ?_, fun hcomm' => absurd hcomm hcomm'⟩
    exact (hQ.trans (inf_le_inf hEle le_rfl)).trans hcent
  · -- `[M_σ∩M*, M∩M*] ≠ 1`: apply Lemma 13.1.
    have hpτ2Mstar : p ∉ tau2 Mstar :=
      not_mem_tau2_of_interaction hG h hMstarMax hpπE hcomm hnc
    have hpσMstar : p ∈ S10.sigma Mstar :=
      (prime_mem_sigma_or_tau2 hG hMmax hPM hPne hPp hMstar).resolve_right hpτ2Mstar
    have hpτ1Mstar : p ∉ tau1 Mstar := fun ht => tau1_subset_sigma_compl Mstar ht hpσMstar
    refine ⟨?_, ?_, ?_⟩
    · -- (a)
      intro Q hQ hQp
      exact pSubgroup_centralizes_Msigma_inf hG h hMstarMax hpπE hpπMstar
        hpτ1Mstar hpτ2Mstar hnc hQ hQp
    · -- (b): per-prime reduction over the prime-power subgroups of `Q`.
      intro Q hQ hQpi
      refine le_centralizer_of_forall_prime_isPGroup ?_
      intro r hr R hRQ hRr
      rcases eq_or_ne R ⊥ with hRbot | hRbot
      · rw [hRbot]; exact bot_le
      · haveI : Fact r.Prime := ⟨hr⟩
        have hRE : R ≤ E := hRQ.trans (hQ.trans inf_le_left)
        have hRMstar : R ≤ Mstar := hRQ.trans (hQ.trans inf_le_right)
        have hrτ1Mstar : r ∉ tau1 Mstar :=
          hQpi r (mem_primeFactors_of_isPGroup_le hr hRQ hRbot hRr)
        have hrπE : r ∈ (Nat.card ↥E).primeFactors :=
          mem_primeFactors_of_isPGroup_le hr hRE hRbot hRr
        have hrπMstar : r ∈ (Nat.card ↥Mstar).primeFactors :=
          mem_primeFactors_of_isPGroup_le hr hRMstar hRbot hRr
        have hrτ2Mstar : r ∉ tau2 Mstar :=
          not_mem_tau2_of_interaction hG h hMstarMax hrπE hcomm hnc
        exact pSubgroup_centralizes_Msigma_inf hG h hMstarMax hrπE hrπMstar
          hrτ1Mstar hrτ2Mstar hnc (le_inf (hRE.trans hEle) hRMstar) hRr
    · -- (c)
      intro _
      refine ⟨hpσMstar, fun hpτ1M => ?_⟩
      have hideal : S10.idealPrime p G :=
        mem_idealPrime_of_tau1_of_interaction hG h hMstarMax hpπE hpπMstar
          hpτ1Mstar hpτ2Mstar hcomm hnc hpτ1M
      rw [S10.mem_beta_iff]
      refine ⟨?_, hideal⟩
      rw [S10.mem_alpha_iff]
      refine ⟨hpπMstar, ?_⟩
      rw [pRank_eq_of_mem_sigma hpσMstar]
      exact ((S10.mem_idealPrime_iff p G).mp hideal).1

end OddOrder.BG.Ch3.S13
