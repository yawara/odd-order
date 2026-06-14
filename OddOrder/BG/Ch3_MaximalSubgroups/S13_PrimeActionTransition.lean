/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Theorem1310

/-!
# BG §13 (cont.): Corollary 13.11 + Lemma 13.12/13.13（active leaf / hub）

**Scope**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §13 末尾 (mmd L3696–3780, pp. 103–104)。

§13 後半 frontier の **active leaf**。凍結クラスタ（Lemma 13.7 / 13.8 /
Theorem 13.9 / 13.10）は上流ファイルへ prefix-split 済（`S13_Theorem1310` が束ねる）。
本ファイルは下流 import（`S14_TypePCounting`, `AxiomsCheck`）の入口を兼ねる hub。

* **Corollary 13.11** `E3_not_regular_consequences`: 13.10 + 13.7。
* （frontier）**Lemma 13.12 / 13.13**: §14 Prop 14.2 funnel が直接依存（issue 2006）。
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- In a finite cyclic group, a subgroup of prime order is unique: two subgroups of the same
prime order `q` coincide. (`H ⊔ K` is elementary abelian of exponent `q` and cyclic, hence of
order dividing `q`, forcing `H = H ⊔ K = K`.) Used for BG Cor 13.11(d). -/
theorem eq_of_card_eq_prime_of_isCyclic {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {q : ℕ} (hq : q.Prime) {H K : Subgroup A}
    (hH : Nat.card ↥H = q) (hK : Nat.card ↥K = q) : H = K := by
  haveI : Fact q.Prime := ⟨hq⟩
  letI : CommGroup A := IsCyclic.commGroup
  have hHel : H.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hH
  have hKel : K.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hK
  have hcent : H ≤ Subgroup.centralizer (K : Set A) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
  have hsupel : (H ⊔ K).IsElementaryAbelian q := hHel.sup_of_le_centralizer hKel hcent
  haveI : IsCyclic ↥(H ⊔ K) := inferInstance
  have hexp : Monoid.exponent ↥(H ⊔ K) ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => hsupel.2 x)
  have hcarddvd : Nat.card ↥(H ⊔ K) ∣ q := by rwa [IsCyclic.exponent_eq_card] at hexp
  have hcardle : Nat.card ↥(H ⊔ K) ≤ q := Nat.le_of_dvd hq.pos hcarddvd
  have hHK : H = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH]; exact hcardle)
  have hKK : K = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hK]; exact hcardle)
  exact hHK.trans hKK.symm

/-- `G`-level form of `eq_of_card_eq_prime_of_isCyclic`: two order-`q` subgroups of `G` both
contained in a cyclic subgroup `A` coincide. -/
theorem eq_of_card_eq_prime_of_le_isCyclic {A : Subgroup G} [Finite ↥A] (hAcyc : IsCyclic ↥A)
    {q : ℕ} (hq : q.Prime) {H K : Subgroup G} (hHA : H ≤ A) (hKA : K ≤ A)
    (hH : Nat.card ↥H = q) (hK : Nat.card ↥K = q) : H = K := by
  haveI := hAcyc
  have hH' : Nat.card ↥(H.subgroupOf A) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv]; exact hH
  have hK' : Nat.card ↥(K.subgroupOf A) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv]; exact hK
  have hEq : H.subgroupOf A = K.subgroupOf A := eq_of_card_eq_prime_of_isCyclic hq hH' hK'
  have hmap := congrArg (Subgroup.map A.subtype) hEq
  rwa [Subgroup.map_subgroupOf_eq_of_le hHA, Subgroup.map_subgroupOf_eq_of_le hKA] at hmap

/-- **BG Corollary 13.11** (mmd L3696; 結論は PDF p.103 から画像読みで復元): `E₃≠1` かつ `E₃` が
`M_σ` に regular 作用しないなら (a) `E₁≠1`; (b) `E=E₁E₃`; (c) `E` は `M_σ` に prime 作用;
(d) すべての `X∈ℰ¹(E)` は `E` で正規。 -/
theorem E3_not_regular_consequences [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE3 : E₃ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn (S10.Msigma M) E₃) :
    E₁ ≠ ⊥ ∧ E = E₁ ⊔ E₃ ∧ ActsPrimeOn (S10.Msigma M) E ∧
    (∀ q : ℕ, ∀ X : Subgroup G, X ∈ elemAbelianOfRank G q 1 → X ≤ E →
      E ≤ Subgroup.normalizer (X : Set G)) := by
  classical
  have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
  -- From `¬reg` and `E₃` prime on `M_σ`: some `x ∈ E₃#` has `C_{M_σ}(x) ≠ 1`.
  have hxex : ∃ x ∈ E₃, x ≠ 1 ∧ S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    exact hreg (fun x hxE3 hx1 => by rw [fixedByElement_def]; exact hcon x hxE3 hx1)
  obtain ⟨x, hxE3, hxne, hxC⟩ := hxex
  -- `τ₂(M)` empty (`E₂ = ⊥`): an `A ∈ ℰ_p²(E)` with `p ∈ τ₂` would force `C_{M_σ}(x) = 1`.
  have hE2 : E₂ = ⊥ := by
    by_contra hE2ne
    obtain ⟨pp, hpp, hppdvd⟩ :=
      (Nat.card ↥E₂).exists_prime_and_dvd (fun hc => hE2ne (Subgroup.card_eq_one.mp hc))
    haveI : Fact pp.Prime := ⟨hpp⟩
    have hc2 : Nat.card ↥(E₂.subgroupOf E) = Nat.card ↥E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hppτ2 : pp ∈ tau2 M :=
      h.E₂_hall.1 pp (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hpp, hppdvd, Nat.card_pos.ne'⟩)
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hppτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hppτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  -- (b) `E = E₁ ⊔ E₃` and (a) `E₁ ≠ ⊥`.
  have hEsup : E = E₁ ⊔ E₃ := by rw [h.eq_sup hG, hE2, sup_bot_eq]
  have hE1ne : E₁ ≠ ⊥ := h.E1_ne_bot_of_E2_eq_bot hG hE2
  -- Thm 13.10 contrapositive: every rank-1 `P ≤ E₁` centralizes `E₃`.
  have hAllCent : ∀ pp : ℕ, pp.Prime → ∀ P : Subgroup G, P ∈ elemAbelianOfRank G pp 1 → P ≤ E₁ →
      P ≤ Subgroup.centralizer (E₃ : Set G) := by
    intro pp hpp P hPmem hPE1
    by_contra hPnc
    exact hreg (E1_regular_on_E3_of_noncentralize hG h ⟨pp, hpp, P, hPmem, hPE1, hPnc⟩).2.1
  -- `E₁` does not act regularly on `E₃` (a rank-1 `P ≤ E₁` centralizes the nontrivial `E₃`).
  have hE1nreg : ¬ ActsRegularlyOn E₃ E₁ := by
    obtain ⟨pp, hpp, hppdvd⟩ :=
      (Nat.card ↥E₁).exists_prime_and_dvd (fun hc => hE1ne (Subgroup.card_eq_one.mp hc))
    haveI : Fact pp.Prime := ⟨hpp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' pp hppdvd
    have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = pp := by
      rw [Nat.card_zpowers]; exact (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
    have hPmem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G pp 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
    have hPC : Subgroup.zpowers (g : G) ≤ Subgroup.centralizer (E₃ : Set G) :=
      hAllCent pp hpp _ hPmem (Subgroup.zpowers_le.mpr g.2)
    have hgne : g ≠ 1 := by intro hc; rw [hc, orderOf_one] at hg; exact hpp.ne_one hg.symm
    have hg1 : (g : G) ≠ 1 := fun hc => hgne (Subtype.ext (by simpa using hc))
    have hgCE3 : (g : G) ∈ Subgroup.centralizer (E₃ : Set G) := hPC (Subgroup.mem_zpowers _)
    have hE3sub : E₃ ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
      intro e he; rw [Subgroup.mem_centralizer_iff]; intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp hgCE3 e he).symm
    rw [ActsRegularlyOn]; push_neg
    refine ⟨(g : G), g.2, hg1, ?_⟩
    rw [fixedByElement_def]
    intro hbot
    exact hE3 (le_bot_iff.mp (hbot ▸ le_inf le_rfl hE3sub))
  -- (c) `E` acts in a prime manner on `M_σ`.
  have hEprime : ActsPrimeOn (S10.Msigma M) E := hEsup ▸ E1E3_actsPrime hG h hE1ne hE1nreg
  refine ⟨hE1ne, hEsup, hEprime, ?_⟩
  -- (d) every `X ∈ ℰ¹(E)` is normal in `E`. TODO (reconstruction gap — see notes).
  sorry


end OddOrder.BG.Ch3.S13
