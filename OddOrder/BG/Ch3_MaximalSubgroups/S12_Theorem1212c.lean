/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212b

/-!
# BG §12: Theorem 12.12 — three-case assembly

**スコープ**: BG Theorem 12.12 (mmd L3336-3373) の最終組立。仮定は「すべての
`(τ₁(M) ∪ τ₃(M))`-元 `e ∈ E#` で `C_{M_σ}(e) = 1`」(`hreg`)。結論 `FrobFactConclusion M E`:
(a) `E` は abelian normal `A₀` を含み `∀ x ∈ M_σ#, C_E(x) ⊆ A₀`;
(b) `E` は `E` と同 exponent の `E₀` を含み `E₀ M_σ` は kernel `M_σ` の Frobenius 群。

**証明の 3 ケース** (BG L3341-3344):

* **Case 1** (`τ₂(M) = ∅`, BG: `E = E₁E₃`): すべての `e ∈ E#` の素因数が `τ₁ ∪ τ₃` に入る
  ので `hreg` は無条件化し、`A₀ = 1`, `E₀ = E` で `frobFact_of_regular_all` が直ちに与える。
* **Case 2** (`τ₂(M) ≠ ∅`, 非可換 Sylow `p`): `frobFact_of_nonabelianSylow` (Theorem 12.7 経由)。
* **Case 3** (`τ₂(M) ≠ ∅`, すべての Sylow が可換): `frobFact_of_abelianSylow` (Lemma 12.8 +
  per-prime cyclic `Z_p` 構成の集約; **本ファイルの主たる残務**)。

ケース分けは「`|E|` を割る `τ₂`-素数で非可換 Sylow をもつものが存在するか」で行う。`τ₂(M)` の
素数はすべて `|E|` を割る (`p ∉ σ(M)` ゆえ `p ∤ |M_σ|`、かつ `pRank_M = 2` から `p ∣ |M|`) ので、
素数性は `Nat.prime_of_mem_primeFactors` で自動的に得られる。
-/

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.Isaacs.Ch06
open scoped Pointwise
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- A `π`-subgroup `N` is contained in any **normal** Hall `π`-subgroup `H`. (Companion to
`Subgroup.IsPiGroup.normal_le_hall`, which assumes the *small* subgroup normal; here the *Hall*
one is normal and `N` is arbitrary.) `H ⊔ N = HN` is a `π`-group (its order divides `|H|·|N|`), so
Hall maximality forces `H ⊔ N = H`. -/
theorem isPiSubgroup_le_of_normal_isHall [Finite G] {π : Set ℕ} {H N : Subgroup G} [H.Normal]
    (hH : Ch03.IsHallSubgroup π H) (hN : Ch03.Subgroup.IsPiGroup π N) : N ≤ H := by
  have hSup_pi : Ch03.Subgroup.IsPiGroup π (H ⊔ N : Subgroup G) := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, _⟩ := hq
    have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) * Nat.card ↥(H ⊓ N : Subgroup G)
        = Nat.card ↥H * Nat.card ↥N := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card H N
      rwa [show (↑H * ↑N : Set G) = ↑(H ⊔ N : Subgroup G) from
        (Subgroup.normal_mul H N).symm] at h_hk
    have h_dvd_prod : q ∣ Nat.card ↥H * Nat.card ↥N := by
      rw [← h_card_eq]; exact hq_dvd.mul_right _
    rcases hq_prime.dvd_mul.mp h_dvd_prod with hH_dvd | hN_dvd
    · exact hH.1 q (Nat.mem_primeFactors.mpr ⟨hq_prime, hH_dvd, Nat.card_pos.ne'⟩)
    · exact hN q (Nat.mem_primeFactors.mpr ⟨hq_prime, hN_dvd, Nat.card_pos.ne'⟩)
  have h_card_dvd : Nat.card ↥(H ⊔ N : Subgroup G) ∣ Nat.card ↥H :=
    hH.card_dvd_of_isPiGroup hSup_pi
  have h_card_eq : Nat.card ↥(H ⊔ N : Subgroup G) = Nat.card ↥H :=
    Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd)
      (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective le_sup_left))
  have h_sup_eq : (H ⊔ N : Subgroup G) = H :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left h_card_eq.le).symm
  intro x hx
  have hx_sup : x ∈ (H ⊔ N : Subgroup G) := Subgroup.mem_sup_right hx
  rwa [h_sup_eq] at hx_sup

/-- **Per-prime `Z_p` extraction** for the abelian-Sylow case (`p ∈ τ₂(M)`). Combining
`exists_elemAb_rank_two_le_E_of_tau2`, the Sylow extension `A ≤ S`, the abelianness `habel`, the
Lemma 12.8(c) chain (`sylow_chain_of_abelianSylow`, giving `S ≤ E`), and the per-prime capstone
`exists_cyclic_Enormal_regular_of_abelianSylow`, we obtain a cyclic `p`-subgroup `Z ≤ E`,
normalized by `E`, of the same exponent as a Sylow `p`-subgroup `S ≤ E`, acting regularly on
`M_σ`. (`Z ⊴ E` follows from `E ≤ N_G(Z)`; the `Z_p` for distinct `p ∈ τ₂(M)` will assemble into
an internal direct product `∏ Z_p ≤ E`.) -/
theorem exists_regular_cyclic_of_mem_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M)
    (habel : ∀ S : Sylow p G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    ∃ Z : Subgroup G, Z ≤ E ∧ IsCyclic ↥Z ∧ Z ≠ ⊥ ∧ IsPGroup p ↥Z ∧
      E ≤ Subgroup.normalizer (Z : Set G) ∧
      (∃ S : Sylow p G, (S : Subgroup G) ≤ E ∧
        Monoid.exponent ↥Z = Monoid.exponent ↥(S : Subgroup G)) ∧
      ∀ z ∈ Z, z ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
  obtain ⟨S, hAS⟩ := hA.1.isPGroup.exists_le_sylow
  have hSab : IsMulCommutative ↥(S : Subgroup G) := habel S
  have hSE : (S : Subgroup G) ≤ E :=
    (le_centralizer_of_le_of_le hSab le_rfl hAS).trans (centralizer_le_E_of_tau2 hG h hp hA hAE).1
  have hSM : (S : Subgroup G) ≤ M := hSE.trans h.E_le
  obtain ⟨Z, hZS, hZcyc, hZne, hZN, hZexp, hZreg⟩ :=
    exists_cyclic_Enormal_regular_of_abelianSylow hG h hp hA hAE hAS hSM hSab hreg
  exact ⟨Z, hZS.trans hSE, hZcyc, hZne, S.isPGroup'.to_le hZS, hZN, ⟨S, hSE, hZexp⟩, hZreg⟩

/-- **BG Theorem 12.12, Case 3, part (a)** (mmd L3345 "Obviously `A₀ = E₂` satisfies (a)"):
in the abelian-Sylow regime, `A₀ = E₂` is an abelian normal subgroup of `E` (Lemma 12.8(a)) with
`C_E(x) ⊆ E₂` for every `x ∈ M_σ#`. The containment holds because `C_E(x)` is a `τ₂(M)`-group:
any prime `q ∣ |C_E(x)|` with `q ∈ τ₁(M) ∪ τ₃(M)` would give an element `a ∈ E#` of order `q`
centralizing `x`, so `x ∈ M_σ ⊓ C_G(a) = 1` by `hreg`, contradiction; hence `q ∈ τ₂(M)`, and the
`τ₂`-subgroup `C_E(x)` lies in the normal Hall `τ₂`-subgroup `E₂`. -/
theorem frobFact_partA_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M)
    (habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
      ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    ∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative ↥A₀ ∧
      E ≤ Subgroup.normalizer ((A₀ : Subgroup G) : Set G) ∧
      ∀ x ∈ S10.Msigma M, x ≠ 1 → E ⊓ Subgroup.centralizer ({x} : Set G) ≤ A₀ := by
  classical
  obtain ⟨p, hpE, hp⟩ := hτ2
  haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpE⟩
  obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
  obtain ⟨S, hAS⟩ := hA.1.isPGroup.exists_le_sylow
  have hSab : IsMulCommutative ↥(S : Subgroup G) := habel p hpE hp S
  obtain ⟨⟨hE₂ab, hE₂norm⟩, _⟩ := E2_abelian_of_abelianSylow hG h hp hA hAE S hAS hSab
  refine ⟨E₂, h.E₂_le, hE₂ab, hE₂norm, ?_⟩
  intro x hxMσ hxne
  -- `C_E(x) = E ⊓ C_G(x)` is a `τ₂`-subgroup of `E`; the normal Hall `τ₂`-subgroup `E₂` contains it.
  haveI : ((E₂).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₂_le).mpr hE₂norm
  have hpi : Ch03.Subgroup.IsPiGroup (tau2 M)
      ((E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf E) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    haveI : Fact q.Prime := ⟨hqp⟩
    have hqE : q ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans (Subgroup.card_dvd_of_le inf_le_left),
        Nat.card_pos.ne'⟩
    by_contra hqnτ2
    obtain ⟨a, ha_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(E ⊓ Subgroup.centralizer
      ({x} : Set G))) q hqd
    have haE : (a : G) ∈ E := (Subgroup.mem_inf.mp a.2).1
    have haCx : (a : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp a.2).2
    have hane : (a : G) ≠ 1 := by
      intro hc
      rw [← Subgroup.orderOf_coe, hc, orderOf_one] at ha_ord
      exact hqp.ne_one ha_ord.symm
    have ha_ordG : orderOf (a : G) = q := by rw [Subgroup.orderOf_coe]; exact ha_ord
    have hq13 : q ∈ tau1 M ∪ tau3 M := by
      rcases h.mem_tau_union_of_mem_primeFactors hG hqE with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hqnτ2
      · exact Or.inr h3
    have hreg_a : S10.Msigma M ⊓ Subgroup.centralizer ({(a : G)} : Set G) = ⊥ := by
      refine hreg (a : G) haE hane ?_
      intro r hr
      rw [ha_ordG, hqp.primeFactors, Finset.mem_singleton] at hr
      rwa [hr]
    have hxmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hxMσ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact (Subgroup.mem_centralizer_iff.mp haCx x (Set.mem_singleton x)).symm
    rw [hreg_a, Subgroup.mem_bot] at hxmem
    exact hxne hxmem
  have hle := isPiSubgroup_le_of_normal_isHall (H := (E₂).subgroupOf E)
    (N := (E ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf E) h.E₂_hall hpi
  intro y hy
  have hyE : y ∈ E := (Subgroup.mem_inf.mp hy).1
  have : (⟨y, hyE⟩ : ↥E) ∈ (E₂).subgroupOf E := hle (Subgroup.mem_subgroupOf.mpr hy)
  exact Subgroup.mem_subgroupOf.mp this

/-- **BG Theorem 12.12, Case 3** (mmd L3344-3373): in the abelian-Sylow regime, with `τ₂(M)`
nonempty, the conclusion `FrobFactConclusion M E` holds. Here `A₀ = E₂` (abelian normal Hall
`τ₂`-subgroup of `E`, by Lemma 12.8(a)), and `E₀ = E₁E₃ · ∏_{p ∈ τ₂} Z_p`, where each `Z_p` is a
cyclic normal subgroup of `E` of the same exponent as a Sylow `p`-subgroup `S_p ≤ E` and acting
regularly on `M_σ` (`exists_cyclic_Enormal_regular_of_abelianSylow`).

`habel` provides that every Sylow `p`-subgroup of `G` (for `p ∈ τ₂(M)` dividing `|E|`) is abelian;
`hτ2` witnesses the nonemptiness of `τ₂(M) ∩ π(E)`.

**TODO** (Lane F): the `τ₂`-product aggregation `E₀` together with `exp(E₀) = exp(E)` and the
regularity of `E₀` (via `inf_centralizer_eq_bot_of_forall_prime_order`, reducing to prime-order
elements: those of `τ₁ ∪ τ₃`-order use `hreg`, those of `τ₂`-order lie in the relevant `Z_p`). -/
theorem frobFact_of_abelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M)
    (habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
      ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  sorry

/-- **BG Theorem 12.12** (mmd L3336): suppose `C_{M_σ}(e) = 1` for every
`(τ₁(M) ∪ τ₃(M))`-element `e ∈ E#`. Then
(a) `E` contains an abelian normal subgroup `A₀` with `C_E(x) ⊆ A₀` for all `x ∈ M_σ#`, and
(b) `E` contains a subgroup `E₀` of the same exponent as `E` such that `E₀ M_σ` is a Frobenius
group with Frobenius kernel `M_σ`.

(Scaffold moved here from `S12_E.lean`.) Proof by the three-case split described in the file
header. The case selector is whether some `τ₂(M)`-prime dividing `|E|` has a nonabelian Sylow
`p`-subgroup in `G`. -/
theorem frobenius_factorization_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  by_cases hnonab : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M ∧
      ∃ S : Sylow p G, ¬ IsMulCommutative ↥(S : Subgroup G)
  · -- **Case 2**: a `τ₂`-prime with a nonabelian Sylow.
    obtain ⟨p, hpE, hp, hS⟩ := hnonab
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpE⟩
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hp
    exact frobFact_of_nonabelianSylow hG h hp hA hAE hS hreg
  · -- No `τ₂`-prime has a nonabelian Sylow: all relevant Sylows are abelian.
    have habel : ∀ q, q ∈ (Nat.card ↥E).primeFactors → q ∈ tau2 M →
        ∀ S : Sylow q G, IsMulCommutative ↥(S : Subgroup G) := by
      intro q hqE hq S
      by_contra hc
      exact hnonab ⟨q, hqE, hq, S, hc⟩
    by_cases hτ2 : ∃ p ∈ (Nat.card ↥E).primeFactors, p ∈ tau2 M
    · -- **Case 3**: `τ₂(M) ≠ ∅`, abelian Sylows.
      exact frobFact_of_abelianSylow hG h hτ2 habel hreg
    · -- **Case 1**: no `τ₂`-prime divides `|E|`, so `E = E₁E₃` and `hreg` is unconditional.
      refine frobFact_of_regular_all hG h (h.E_ne_bot hG) ?_
      intro e heE hene
      refine hreg e heE hene ?_
      intro r hr
      obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
      have hrE : r ∈ (Nat.card ↥E).primeFactors := by
        exact Nat.mem_primeFactors.mpr ⟨hrp, hrd.trans (E.orderOf_dvd_natCard heE), Nat.card_pos.ne'⟩
      have hru : r ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
        h.mem_tau_union_of_mem_primeFactors hG hrE
      have hrnτ2 : r ∉ tau2 M := fun hr2 => hτ2 ⟨r, hrE, hr2⟩
      rcases hru with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 hrnτ2
      · exact Or.inr h3

end OddOrder.BG.Ch3.S12
