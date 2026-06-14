/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_Theorem1310
import Mathlib.GroupTheory.NoncommCoprod

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
    (∀ q : ℕ, q.Prime → ∀ X : Subgroup G, X ∈ elemAbelianOfRank G q 1 → X ≤ E →
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
  -- (d) every prime-order `X ≤ E` is normal in `E`.
  intro q hqp X hXmem hXE
  haveI : Fact q.Prime := ⟨hqp⟩
  have hXcard : Nat.card ↥X = q := by simpa using hXmem.2
  have hEN3 : E ≤ Subgroup.normalizer ((E₃ : Subgroup G) : Set G) := h.E3_normal hG
  -- `|E₁|`, `|E₃|` are coprime (`τ₁ ∩ τ₃ = ∅`).
  have hcop13 : Nat.Coprime (Nat.card ↥E₁) (Nat.card ↥E₃) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    exact not_mem_tau3_of_mem_tau1
      (h.isPiGroup_tau1 r (Nat.mem_primeFactors.mpr
        ⟨hr, hrd.trans (Nat.gcd_dvd_left _ _), Nat.card_pos.ne'⟩))
      (h.isPiGroup_tau3 r (Nat.mem_primeFactors.mpr
        ⟨hr, hrd.trans (Nat.gcd_dvd_right _ _), Nat.card_pos.ne'⟩))
  by_cases hqE3 : q ∣ Nat.card ↥E₃
  · -- τ₃ case: `X ≤ E₃`, characteristic in the cyclic `E₃ ⊴ E`.
    have hqnE1 : ¬ q ∣ Nat.card ↥E₁ := by
      intro hd
      exact hqp.ne_one (Nat.dvd_one.mp (hcop13 ▸ Nat.dvd_gcd hd hqE3))
    have hcopXE1 : Nat.Coprime (Nat.card ↥X) (Nat.card ↥E₁) :=
      hXcard ▸ (hqp.coprime_iff_not_dvd.mpr hqnE1)
    have hXE3 : X ≤ E₃ :=
      le_of_le_sup_of_coprime_card (h.E₁_le.trans hEN3)
        (by rw [sup_comm, ← hEsup]; exact hXE) hcopXE1
    exact E_le_normalizer_of_le_E3 hG h hXE3
  · -- τ₁ case: `q ∣ |E₁|`; `X` equals the unique order-`q` subgroup of `E₁` modulo `E₃`.
    haveI : IsCyclic ↥E₁ := h.E1_isCyclic hG
    haveI : IsCyclic ↥E₃ := h.E3_isCyclic hG
    have hE1NE3 : E₁ ≤ Subgroup.normalizer (E₃ : Set G) := h.E₁_le.trans (h.E3_normal hG)
    -- `|E| = |E₁| * |E₃|`, so from `q ∣ |X| ∣ |E|` and `q ∤ |E₃|` we get `q ∣ |E₁|`.
    have hcardE : Nat.card ↥E = Nat.card ↥E₁ * Nat.card ↥E₃ := by
      rw [hEsup]
      exact card_sup_eq_mul_of_le_normalizer_of_disjoint hE1NE3
        (Subgroup.inf_eq_bot_of_coprime hcop13)
    have hqE : q ∣ Nat.card ↥E := by
      have := Subgroup.card_dvd_of_le hXE; rwa [hXcard] at this
    have hqE1 : q ∣ Nat.card ↥E₁ := by
      rw [hcardE] at hqE
      exact (hqp.dvd_mul.mp hqE).resolve_right hqE3
    -- Build `P₀ = ⟨g⟩` of order `q` inside `E₁`, centralizing `E₃` (Thm 13.10 contrapositive).
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqE1
    set P₀ : Subgroup G := Subgroup.zpowers (g : G) with hP₀def
    have hP₀card : Nat.card ↥P₀ = q := by
      rw [hP₀def, Nat.card_zpowers]
      exact (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
    have hP₀E1 : P₀ ≤ E₁ := Subgroup.zpowers_le.mpr g.2
    have hP₀mem : P₀ ∈ elemAbelianOfRank G q 1 :=
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hP₀card, by rw [hP₀card, pow_one]⟩
    have hP₀cent : P₀ ≤ Subgroup.centralizer (E₃ : Set G) := hAllCent q hqp P₀ hP₀mem hP₀E1
    have hP₀E : P₀ ≤ E := hP₀E1.trans h.E₁_le
    -- `E` normalizes `P₀`: `E₁` does (char in cyclic `E₁`), and `E₃` does (centralizes it).
    have hE1NP₀ : E₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
      haveI : (P₀.subgroupOf E₁).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
      intro e he
      have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := E₁)
        (C := P₀.subgroupOf E₁) (Subgroup.le_normalizer he)
      rwa [Subgroup.map_subgroupOf_eq_of_le hP₀E1] at hmem
    have hE3NP₀ : E₃ ≤ Subgroup.normalizer (P₀ : Set G) := by
      have hE3cP₀ : E₃ ≤ Subgroup.centralizer (P₀ : Set G) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Subgroup.mem_centralizer_iff.mp (hP₀cent hu) e he).symm
      exact hE3cP₀.trans (Subgroup.centralizer_le_normalizer _)
    have hENP₀ : E ≤ Subgroup.normalizer (P₀ : Set G) :=
      hEsup ▸ sup_le hE1NP₀ hE3NP₀
    -- `D := P₀ ⊔ E₃` is cyclic (internal direct product of commuting coprime cyclics).
    set D : Subgroup G := P₀ ⊔ E₃ with hDdef
    have hcopP₀E3 : Nat.Coprime (Nat.card ↥P₀) (Nat.card ↥E₃) :=
      hP₀card ▸ (hqp.coprime_iff_not_dvd.mpr hqE3)
    have hP₀E3bot : P₀ ⊓ E₃ = ⊥ := Subgroup.inf_eq_bot_of_coprime hcopP₀E3
    have hcomm : ∀ (m : ↥P₀) (n : ↥E₃), Commute (P₀.subtype m) (E₃.subtype n) := by
      intro m n
      show (m : G) * (n : G) = (n : G) * (m : G)
      exact (Subgroup.mem_centralizer_iff.mp (hP₀cent m.2) (n : G) n.2).symm
    haveI : IsCyclic ↥D := by
      have hinj : Function.Injective (MonoidHom.noncommCoprod P₀.subtype E₃.subtype hcomm) :=
        (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
          ⟨P₀.subtype_injective, E₃.subtype_injective, by
            rw [P₀.range_subtype, E₃.range_subtype]; exact disjoint_iff.mpr hP₀E3bot⟩
      have hrange : (MonoidHom.noncommCoprod P₀.subtype E₃.subtype hcomm).range = D := by
        rw [MonoidHom.noncommCoprod_range, P₀.range_subtype, E₃.range_subtype, hDdef]
      have hprodcyc : IsCyclic (↥P₀ × ↥E₃) :=
        Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hcopP₀E3⟩
      exact (((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr hrange)).isCyclic).mp hprodcyc
    -- `E` normalizes `D` (normalizes both `P₀` and `E₃`).
    have hEND : E ≤ Subgroup.normalizer (D : Set G) := le_normalizer_sup hENP₀ hEN3
    -- `X ⊔ E₃ = P₀ ⊔ E₃ = D`, via the unique order-`q` subgroup of the cyclic quotient `E/E₃`.
    haveI hE₃subN : (E₃.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.E₃_le).mpr hEN3
    set mk : ↥E →* (↥E ⧸ E₃.subgroupOf E) := QuotientGroup.mk' (E₃.subgroupOf E) with hmkdef
    -- the quotient `↥E ⧸ E₃.subgroupOf E` is cyclic (surjective image of cyclic `↥E₁`).
    haveI hQcyc : IsCyclic (↥E ⧸ E₃.subgroupOf E) := by
      refine isCyclic_of_surjective (mk.comp (Subgroup.inclusion h.E₁_le)) ?_
      intro y
      induction y using QuotientGroup.induction_on with
      | _ e =>
        have hecoe : (e : G) ∈ (↑(E₁ ⊔ E₃) : Set G) := by
          rw [← hEsup]; exact e.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right E₁ E₃ hE1NE3] at hecoe
        obtain ⟨a, ha, b, hb, hab⟩ := hecoe
        rw [SetLike.mem_coe] at ha hb
        refine ⟨⟨a, ha⟩, ?_⟩
        rw [MonoidHom.comp_apply]
        show mk (Subgroup.inclusion h.E₁_le ⟨a, ha⟩) = mk e
        rw [hmkdef, QuotientGroup.mk'_eq_mk']
        refine ⟨⟨b, h.E₃_le hb⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]; exact hb
        · apply Subtype.ext
          show a * b = (e : G)
          exact hab
    -- both `X` and `P₀` are disjoint from `E₃` (orders coprime), so inject into the quotient.
    have hcopXE3 : Nat.Coprime (Nat.card ↥X) (Nat.card ↥E₃) :=
      hXcard ▸ (hqp.coprime_iff_not_dvd.mpr hqE3)
    have hXE3bot : X ⊓ E₃ = ⊥ := Subgroup.inf_eq_bot_of_coprime hcopXE3
    -- helper: card of the image of a subgroup `K ≤ E` disjoint from `E₃` equals `|K|`.
    have hcardmap : ∀ (K : Subgroup G), K ≤ E → K ⊓ E₃ = ⊥ →
        Nat.card ↥((K.subgroupOf E).map mk) = Nat.card ↥(K.subgroupOf E) := by
      intro K hKE hKbot
      have hkerbot : (E₃.subgroupOf E) ⊓ (K.subgroupOf E) = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hz
        have : (z : G) ∈ K ⊓ E₃ := Subgroup.mem_inf.mpr ⟨hz.2, hz.1⟩
        rw [hKbot, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact Subtype.ext this
      have h1 : Nat.card ↥((K.subgroupOf E).map mk) = (E₃.subgroupOf E).relIndex (K.subgroupOf E) := by
        rw [← Subgroup.relIndex_ker, hmkdef, QuotientGroup.ker_mk']
      rw [h1, Subgroup.relIndex,
        Subgroup.subgroupOf_eq_bot.mpr (disjoint_iff.mpr hkerbot), Subgroup.index_bot]
    have hcardXsub : Nat.card ↥(X.subgroupOf E) = q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXE).toEquiv]; exact hXcard
    have hcardP₀sub : Nat.card ↥(P₀.subgroupOf E) = q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀E).toEquiv]; exact hP₀card
    have hmapXcard : Nat.card ↥((X.subgroupOf E).map mk) = q := by
      rw [hcardmap X hXE hXE3bot, hcardXsub]
    have hmapP₀card : Nat.card ↥((P₀.subgroupOf E).map mk) = q := by
      rw [hcardmap P₀ hP₀E hP₀E3bot, hcardP₀sub]
    have hmapeq : (X.subgroupOf E).map mk = (P₀.subgroupOf E).map mk :=
      eq_of_card_eq_prime_of_isCyclic hqp hmapXcard hmapP₀card
    -- pull back: `X.subgroupOf E ⊔ ker = P₀.subgroupOf E ⊔ ker`, then map up to `X ⊔ E₃ = P₀ ⊔ E₃`.
    have hcomapeq := congrArg (Subgroup.comap mk) hmapeq
    rw [Subgroup.comap_map_eq, Subgroup.comap_map_eq, hmkdef, QuotientGroup.ker_mk'] at hcomapeq
    have hsupsub : (X ⊔ E₃).subgroupOf E = (P₀ ⊔ E₃).subgroupOf E := by
      rw [Subgroup.subgroupOf_sup hXE h.E₃_le, Subgroup.subgroupOf_sup hP₀E h.E₃_le]
      exact hcomapeq
    have hXsupE3 : X ⊔ E₃ = D := by
      have := congrArg (Subgroup.map E.subtype) hsupsub
      rwa [Subgroup.map_subgroupOf_eq_of_le (sup_le hXE h.E₃_le),
        Subgroup.map_subgroupOf_eq_of_le (sup_le hP₀E h.E₃_le), ← hDdef] at this
    -- `X ≤ D`, `X` characteristic in cyclic `D`, `E ≤ N(D)` ⟹ `E ≤ N(X)`.
    have hXD : X ≤ D := hXsupE3 ▸ le_sup_left
    haveI : (X.subgroupOf D).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
    intro e he
    have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := D)
      (C := X.subgroupOf D) (hEND he)
    rwa [Subgroup.map_subgroupOf_eq_of_le hXD] at hmem

/-- Conjugation commutes with `centralizer`: `(C_G(S))^g = C_G(S^g)`. -/
private theorem conj_smul_centralizer (g : G) (S : Subgroup G) :
    MulAut.conj g • Subgroup.centralizer (S : Set G)
      = Subgroup.centralizer ((MulAut.conj g • S : Subgroup G) : Set G) :=
  Subgroup.map_centralizer_eq_of_bijective (S : Set G) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).bijective

/-- **Hall conjugacy into the `τ₁`-piece**: given a `SubgroupESetup M E E₁ E₂ E₃` and a `p`-subgroup
`P ≤ E` with `p ∈ τ₁(M)`, some `E`-conjugate of `P` lands inside the `τ₁`-Hall piece `E₁`. (`↥E` is
solvable; `P.subgroupOf E` is a `τ₁(M)`-π-subgroup, contained in a Hall `τ₁`-subgroup of `↥E`, which
is `↥E`-conjugate to `E₁.subgroupOf E`.) Used to normalize `P` into `E₁` in Lemma 13.12. -/
private theorem exists_conj_le_tau1_piece [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau1 M) {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPE : P ≤ E) :
    ∃ c ∈ E, MulAut.conj c • P ≤ E₁ := by
  classical
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  haveI : IsSolvable ↥E := solvable_of_solvable_injective (Subgroup.inclusion_injective h.E_le)
  have hPEpi : Ch03.Subgroup.IsPiGroup (tau1 M) (P.subgroupOf E) := by
    intro s hs
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv] at hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hs
    exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hp
  obtain ⟨H, hH_hall, _, hPH⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥E))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _) hPEpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map E.subtype with hHGdef
  have hHG_le_E : HG ≤ E := Subgroup.map_subtype_le _
  have hHG_sub : HG.subgroupOf E = H := by
    rw [hHGdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
  have hHG_hall : Ch03.IsHallSubgroup (tau1 M) (HG.subgroupOf E) := hHG_sub ▸ hH_hall
  obtain ⟨w, hwE, hw⟩ :=
    Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_E h.E₁_le hHG_hall h.E₁_hall
  refine ⟨w, hwE, ?_⟩
  have hPHG : P ≤ HG := by
    intro x hx
    rw [hHGdef]
    refine Subgroup.mem_map.mpr ⟨⟨x, hPE hx⟩, ?_, rfl⟩
    have hxsub : (⟨x, hPE hx⟩ : ↥E) ∈ P.subgroupOf E := Subgroup.mem_subgroupOf.mpr hx
    exact hHG_sub ▸ hPH hxsub
  calc MulAut.conj w • P ≤ MulAut.conj w • HG :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPHG
    _ = E₁ := hw

/-- **BG Lemma 13.12** (mmd L3745): if `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `q ∈ τ₂(M)`, `A ∈ ℰ_q²(E)`,
and `C_A(P) ≠ 1`, then `C_{M_σ}(P) = 1`.

Proof (BG L3747): suppose `C_{M_σ}(P) ≠ 1`.  By Corollary 12.6(a),(e), `A ◁ E` and
`P ⊄ C_E(A)`, so `Y = C_A(P)` has order `q`.  By Theorem 13.4, `1 ⊂ C_{M_σ}(P) ⊆ C_{M_σ}(Y)`,
hence `𝓜(C_G(Y)) = {M}` by Corollary 12.6(c).  For `M* ∈ 𝓜(N_G(A))` we have `q ∈ σ(M*)` and
`p ∈ τ₁(M*) ∪ τ₂(M*)` by Lemma 12.11.  The case `p ∈ τ₂(M*)` gives `1 ⊂ C_G(P) ∩ M_σ ⊆ M* ∩ M_σ`,
contrary to Theorem 12.5(e); the case `p ∈ τ₁(M*)` gives `𝓜(C_G(Y)) = {M*}` by Lemma 13.6 for
`M*`, contradicting `𝓜(C_G(Y)) = {M}`.

Statement draft = Lane H (issue 2006, BG 原文逐条照合・S13 context build green); proof = Lane F. -/
theorem Msigma_centralizer_eq_bot_of_tau1_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau1 M) (hq : q ∈ tau2 M)
    {P A : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hA : A ∈ elemAbelianOfRank G q 2) (hAE : A ≤ E)
    (hCAP : A ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  classical
  -- By contradiction: assume `C_{M_σ}(P) ≠ 1`.
  rw [← not_ne_iff]
  intro hCPne
  -- Notation and basic facts.
  have hpσ : p ∉ S10.sigma M := hp.1
  have hqσ : q ∉ S10.sigma M := hq.1
  have hpne_q : p ≠ q := by
    rintro rfl
    have := tau1_pRank_eq_one hp; have := tau2_pRank_eq_two hq; omega
  have hAM : A ≤ M := hAE.trans h.E_le
  have hPM : P ≤ M := hPE.trans h.E_le
  have hPp : IsPGroup p ↥P := hP.1.isPGroup
  have hPne : P ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hP
  have hAcard : Nat.card ↥A = q ^ 2 := hA.2
  have hAcomm : IsMulCommutative ↥A := ⟨⟨hA.1.comm⟩⟩
  haveI : IsSolvable ↥M := hG.solvable_of_mem_maximalSubgroups h.mem_maximal
  haveI : IsSolvable ↥E := solvable_of_solvable_injective (Subgroup.inclusion_injective h.E_le)
  -- `M_σ ⊴ M`, used to conjugate `C_{M_σ}(·)` by elements of `M`.
  have hMnormMσ : M ≤ Subgroup.normalizer ((S10.Msigma M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG _ _
  -- 12.6 bundle for `(M, q, A)`.
  have h126 := elemAb_normal_in_E_of_tau2 hG h hq hA hAE
  -- (1) `A ◁ E`.
  have hENA : E ≤ Subgroup.normalizer (A : Set G) := h126.1.1
  -- A conjugate of `P` (within `E`) lies inside the `τ₁`-Hall piece `E₁`.
  have hPconjE1 : ∃ c ∈ E, MulAut.conj c • P ≤ E₁ := exists_conj_le_tau1_piece hG h hp hPp hPE
  -- (2) `P ⊄ C_E(A)`, i.e. `¬ P ≤ C_G(A)`.
  have hPnotcA : ¬ P ≤ Subgroup.centralizer (A : Set G) := by
    intro hPcA
    obtain ⟨c, hcE, hPcE1⟩ := hPconjE1
    have hcM : c ∈ M := h.E_le hcE
    set Pc : Subgroup G := MulAut.conj c • P with hPcdef
    -- `P^c ≤ C_G(A)` (since `A^c = A` because `c ∈ E ≤ N(A)`).
    have hAc : MulAut.conj c • A = A := conj_smul_eq_self_of_mem_normalizer (hENA hcE)
    have hPcCA : Pc ≤ Subgroup.centralizer (A : Set G) := by
      have : MulAut.conj c • P ≤ MulAut.conj c • Subgroup.centralizer (A : Set G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPcA
      rwa [conj_smul_centralizer, hAc, ← hPcdef] at this
    -- `P^c ≠ 1`, so there is `x ∈ (P^c)#`.
    have hPcne : Pc ≠ ⊥ := by
      rw [hPcdef]; intro hbot
      exact hPne (by simpa using congrArg (MulAut.conj c⁻¹ • ·) hbot)
    obtain ⟨x, hxPc, hxne⟩ := (Subgroup.bot_or_exists_ne_one Pc).resolve_left hPcne
    have hxE1 : x ∈ E₁ := hPcE1 hxPc
    have hxCA : x ∈ Subgroup.centralizer (A : Set G) := hPcCA hxPc
    -- 12.6(e): `C_{M_σ}({x}) = ⊥`.
    have hxbot : S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
      h126.2.2.2.2.1 x hxE1 hxCA hxne
    -- `C_{M_σ}(P^c) ≤ C_{M_σ}({x}) = ⊥`.
    have hCPcbot : S10.Msigma M ⊓ Subgroup.centralizer (Pc : Set G) = ⊥ :=
      le_bot_iff.mp (hxbot ▸ le_inf inf_le_left
        (inf_le_right.trans (Subgroup.centralizer_le
          (Set.singleton_subset_iff.mpr (SetLike.mem_coe.mpr hxPc)))))
    -- transport back: `C_{M_σ}(P) = conj c⁻¹ • C_{M_σ}(P^c) = ⊥`, contradicting `hCPne`.
    apply hCPne
    have hMσc : MulAut.conj c⁻¹ • S10.Msigma M = S10.Msigma M :=
      conj_smul_eq_self_of_mem_normalizer (hMnormMσ (M.inv_mem hcM))
    have hPcc : MulAut.conj c⁻¹ • Pc = P := by
      rw [hPcdef, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    calc S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)
        = (MulAut.conj c⁻¹ • S10.Msigma M) ⊓
            (MulAut.conj c⁻¹ • Subgroup.centralizer (Pc : Set G)) := by
          rw [hMσc, conj_smul_centralizer, hPcc]
      _ = MulAut.conj c⁻¹ • (S10.Msigma M ⊓ Subgroup.centralizer (Pc : Set G)) := by
          rw [Subgroup.smul_inf]
      _ = ⊥ := by rw [hCPcbot, Subgroup.smul_bot]
  -- (3) `Y := A ⊓ C_G(P)` has order `q` and is a line of `A` inside `C_E(P)`.
  set Y : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hYdef
  -- Coprime decomposition `A = C_A(P) × [A, P]` (`A` abelian, `P` acts coprimely).
  have hPNA : P ≤ Subgroup.normalizer (A : Set G) := hPE.trans hENA
  have hcopqp : Nat.Coprime q p :=
    (Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr (Ne.symm hpne_q)
  have hcopAP : Nat.Coprime (Nat.card ↥A) (Nat.card ↥P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp hPp
    rw [hAcard, hk]
    exact (hcopqp.pow_left 2).pow_right k
  obtain ⟨hYdisj, hYsup⟩ :=
    OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp (P := A) (K := P) hPNA hcopAP
  -- rewrite `C_G(P) ⊓ A` as `Y = A ⊓ C_G(P)`.
  rw [inf_comm (Subgroup.centralizer (P : Set G)) A] at hYdisj hYsup
  rw [← hYdef] at hYdisj hYsup
  set W : Subgroup G := ⁅A, P⁆ with hWdef
  -- `[A, P] ≠ ⊥` exactly because `P` does not centralize `A`.
  have hWne : W ≠ ⊥ := by
    rw [hWdef, ne_eq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro hAcP
    exact hPnotcA (Subgroup.le_centralizer_iff.mp hAcP)
  -- both `Y` and `W` are `q`-groups (subgroups of the elementary abelian `A`).
  have hYA : Y ≤ A := inf_le_left
  have hWA : W ≤ A := hYsup ▸ le_sup_right
  have hYq : IsPGroup q ↥Y := hA.1.isPGroup.to_le hYA
  have hWq : IsPGroup q ↥W := hA.1.isPGroup.to_le hWA
  -- `A` centralizes (hence normalizes) all its subgroups (it is abelian).
  have hYNW : Y ≤ Subgroup.normalizer (W : Set G) :=
    ((hYA.trans (le_centralizer_self_of_isElementaryAbelian hA.1)).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWA))).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `|Y| * |W| = |Y ⊔ W| = |A| = q²`.
  have hYWcard : Nat.card ↥Y * Nat.card ↥W = q ^ 2 := by
    rw [← card_sup_eq_mul_of_le_normalizer_of_disjoint hYNW hYdisj, hYsup, hAcard]
  -- both factors are nontrivial: `Y ≠ ⊥` (`hCAP`) and `W ≠ ⊥` (`hWne`).
  have hYne : Y ≠ ⊥ := by rw [hYdef]; exact hCAP
  have hYcardq : q ∣ Nat.card ↥Y :=
    hYq.card_eq_or_dvd.resolve_left (fun h1 => hYne (Subgroup.card_eq_one.mp h1))
  have hWcardq : q ∣ Nat.card ↥W :=
    hWq.card_eq_or_dvd.resolve_left (fun h1 => hWne (Subgroup.card_eq_one.mp h1))
  -- from `|Y| * |W| = q²` with both divisible by `q`: `|Y| = q`.
  have hWcard : Nat.card ↥W = q := by
    obtain ⟨a, ha⟩ := hYcardq
    obtain ⟨b, hb⟩ := hWcardq
    have hqpos := (Fact.out : q.Prime).pos
    have hsq : q ^ 2 = q * q := sq q
    have key : q * q = q * (a * b * q) := by
      rw [← hsq, ← hYWcard, ha, hb]; ring
    have hab : a * b = 1 := by
      have h1 : q = a * b * q := Nat.eq_of_mul_eq_mul_left hqpos key
      nlinarith [h1, hqpos]
    have hb1 : b = 1 := Nat.eq_one_of_mul_eq_one_left hab
    rw [hb, hb1, mul_one]
  have hYcard : Nat.card ↥Y = q := by
    have hh := hYWcard
    rw [hWcard, sq] at hh
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : q.Prime).pos hh
  have hYmem : Y ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hYcard, by rw [hYcard, pow_one]⟩
  have hYE : Y ≤ E := hYA.trans hAE
  have hYcP : Y ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  -- (4) `𝓜(C_G(Y)) = {M}`.
  -- `q ∈ π(E)` (`Y ≤ E`, `|Y| = q`).
  have hqE : q ∈ (Nat.card ↥E).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Nat.card_pos.ne'⟩
    exact (hYcard ▸ Subgroup.card_dvd_of_le hYE)
  -- Theorem 13.4: `C_{M_σ}(P) ⊆ C_{M_σ}(Y)`.
  have h134 : S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) :=
    centralizer_le_centralizer_of_tau1 hG h hp hqE hP hPE hYmem (le_inf hYE hYcP)
  have hCYne : S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := fun hbot =>
    hCPne (le_bot_iff.mp (hbot ▸ h134))
  -- Corollary 12.6(c): `𝓜(C_G(Y)) = {M}`.
  have hMY : maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} :=
    h126.2.2.1 Y hYmem hYA hCYne
  -- (5) Pick `M* ∈ 𝓜(N_G(A))`; it is `≠ M` and contains `P`.
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hAcard] at h1
    have hq1 : q ∣ 1 := h1 ▸ dvd_pow_self q (two_ne_zero)
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp hq1)
  have hNAlt : Subgroup.normalizer (A : Set G) < ⊤ :=
    normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hAM hAne
  obtain ⟨Mstar, hMstarCo, hNAMstar⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (A : Set G))).resolve_left hNAlt.ne
  have hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNAMstar⟩
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  -- `P ≤ N_G(A) ≤ M*` and `M* ≠ M` (12.6(b): `¬ N_G(A) ≤ M`).
  have hPMstar : P ≤ Mstar := ((hPE.trans hENA).trans hNAMstar)
  have hMstarneM : Mstar ≠ M := by
    rintro rfl
    exact h126.2.1.2.2 hNAMstar
  -- (6) Lemma 12.11: `q ∈ σ(M*)` and `p ∈ τ₁(M*) ∪ τ₂(M*)`.
  have htransfer := tau2_transfer_to_maximal hG h hq hA hAE hMstar
  have hqσstar : q ∈ S10.sigma Mstar := (htransfer.1 q Fact.out hq).1
  -- `p ∈ π(E/C_E(A))`: `C_E(A) ⊴ E` and the `p`-Sylow of `E` containing `P` is not in `C_E(A)`.
  have hENcA : E ≤
      Subgroup.normalizer ((E ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hENA.trans (normalizer_le_normalizer_centralizer A))
  haveI hCEAnorm : ((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hENcA
  -- `P.subgroupOf E` is a `p`-group; take a Sylow `p`-subgroup `Sp ⊇ P` of `↥E`.
  have hPEpgroup : IsPGroup p ↥(P.subgroupOf E) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm
  obtain ⟨Sp, hPSp⟩ := hPEpgroup.exists_le_sylow
  have hpidx : p ∈ (((E ⊓ Subgroup.centralizer (A : Set G)).subgroupOf E).index).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Fact.out, ?_, Subgroup.index_ne_zero_of_finite⟩
    refine prime_dvd_index_of_sylow_not_le_of_normal Sp (fun hSple => ?_)
    -- if the Sylow `Sp ⊆ C_E(A)`, then `P ⊆ C_G(A)`, contradicting step 2.
    have hPCA : P ≤ Subgroup.centralizer (A : Set G) := by
      intro x hx
      have hxE : (⟨x, hPE hx⟩ : ↥E) ∈ P.subgroupOf E := Subgroup.mem_subgroupOf.mpr hx
      have hxin := hSple (hPSp hxE)
      rw [Subgroup.mem_subgroupOf] at hxin
      exact (Subgroup.mem_inf.mp hxin).2
    exact hPnotcA hPCA
  have hpτstar : p ∈ tau1 Mstar ∪ tau2 Mstar := htransfer.2.1 p hpidx
  -- (7)–(8): split on `p ∈ τ₂(M*)` vs `p ∈ τ₁(M*)`.
  -- `A ≤ M*` (via `A ≤ N_G(A) ≤ M*`) and `A ≤ M*_σ` (`q ∈ σ(M*)`, `A` a `q`-group).
  have hAMstar : A ≤ Mstar := (Subgroup.le_normalizer).trans hNAMstar
  have hAMσstar : A ≤ S10.Msigma Mstar :=
    le_Msigma_of_mem_elemAbelianOfRank_of_mem_sigma hG hMstarMax Fact.out hqσstar hA hAMstar
  -- `1 ⊂ Y ≤ C_{M*_σ}(P)` (`Y ≤ A ≤ M*_σ` and `Y ≤ C_G(P)`).
  have hCMσstarP : S10.Msigma Mstar ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
    refine fun hbot => hYne (le_bot_iff.mp (hbot ▸ ?_))
    exact le_inf (hYA.trans hAMσstar) hYcP
  -- `P` is a `σ(M*)'`-subgroup (`p ∉ σ(M*)` in both branches).
  have hP_pi : p ∉ S10.sigma Mstar → Subgroup.IsPiSubgroup ((S10.sigma Mstar)ᶜ) P := by
    intro hpσstar s hs
    obtain ⟨hsp, hsd, _⟩ := Nat.mem_primeFactors.mp hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn] at hsd
    rwa [(Nat.prime_dvd_prime_iff_eq hsp Fact.out).mp (hsp.dvd_of_dvd_pow hsd)]
  rcases hpτstar with hpτ1star | hpτ2star
  · -- (8) `p ∈ τ₁(M*)`: contradiction with step 4 via Lemma 13.6 for `M*`.
    have hpσstar : p ∉ S10.sigma Mstar := hpτ1star.1
    -- complement `E* ⊇ P` of `M*_σ` in `M*`.
    obtain ⟨Es, Es1, Es2, Es3, hsetupS, hPEs, _⟩ :=
      exists_subgroupESetup_with_le hG hMstarMax hPMstar (hP_pi hpσstar)
    -- conjugate the setup so that `P` lies in its `τ₁`-Hall piece (Hall conjugacy in `↥E*`).
    obtain ⟨c, hcEs, hPcEs1⟩ := exists_conj_le_tau1_piece hG hsetupS hpτ1star hPp hPEs
    have hcMstar : c ∈ Mstar := hsetupS.E_le hcEs
    set hsetupS' := SubgroupESetup.conj' hsetupS (Mstar.inv_mem hcMstar) with hsetupS'def
    -- `P ≤ conj c⁻¹ • Es1` (the `τ₁`-piece of the conjugated setup).
    have hPEs1' : P ≤ MulAut.conj c⁻¹ • Es1 := by
      have h1 : MulAut.conj c⁻¹ • (MulAut.conj c • P) ≤ MulAut.conj c⁻¹ • Es1 :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPcEs1
      rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
    -- a Sylow `q`-subgroup `S` of `M*_σ` (maximal `q`-subgroup of `M*_σ`).
    obtain ⟨S, hSMσstar, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG hsetupS q
    have hSmax : ∀ T : Subgroup G, T ≤ S10.Msigma Mstar → IsPGroup q ↥T → S ≤ T → S = T :=
      fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
    -- `Y ≤ M*_σ ⊓ C_G(P)`.
    have hYCstar : Y ≤ S10.Msigma Mstar ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf (hYA.trans hAMσstar) hYcP
    -- Lemma 13.6 for `M*`: `𝓜(C_G(Y)) = {M*}`.
    have hMstarY : maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {Mstar} :=
      (maximalContaining_eq_singleton_of_E1 hG hsetupS' hqσstar hPEs1' hPne hYmem hYCstar
        hSMσstar hSq hSmax).1
    -- contradiction with step 4 (`𝓜(C_G(Y)) = {M}`, `M* ≠ M`).
    rw [hMstarY] at hMY
    exact hMstarneM (Set.singleton_injective hMY)
  · -- (7) `p ∈ τ₂(M*)`: contradiction with Theorem 12.5(e) for the original `M`.
    have hpσstar : p ∉ S10.sigma Mstar := hpτ2star.1
    -- complement `E* ⊇ P` of `M*_σ` in `M*`, and a rank-2 `A* ∈ ℰ_p²(E*)`.
    obtain ⟨Es, Es1, Es2, Es3, hsetupS, hPEs, _⟩ :=
      exists_subgroupESetup_with_le hG hMstarMax hPMstar (hP_pi hpσstar)
    obtain ⟨As, hAsmem, hAsEs⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hsetupS hpτ2star
    -- 12.6(a)/M*: `ℰ_p¹(E*) = ℰ¹(A*)`, hence `P ≤ A*`.
    have hPAs : P ≤ As :=
      ((elemAb_normal_in_E_of_tau2 hG hsetupS hpτ2star hAsmem hAsEs).1.2 P hP).mp hPEs
    -- 12.6(c)/M*: `𝓜(C_G(P)) = {M*}`.
    have hMstarCP : maximalSubgroupsContaining (Subgroup.centralizer (P : Set G)) = {Mstar} :=
      (elemAb_normal_in_E_of_tau2 hG hsetupS hpτ2star hAsmem hAsEs).2.2.1 P hP hPAs hCMσstarP
    -- pick `z ∈ (M_σ ⊓ C_G(P))#`; then `z ∈ C_G(P) ≤ M*` and `z ∈ M_σ`, so `M_σ ⊓ M* ≠ ⊥`.
    obtain ⟨z, hzmem, hzne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCPne
    obtain ⟨hzMσ, hzCP⟩ := Subgroup.mem_inf.mp hzmem
    have hCPlt : Subgroup.centralizer (P : Set G) < ⊤ :=
      lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
        (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hPM hPne)
    obtain ⟨Mst', hco', hle'⟩ := (eq_top_or_exists_le_coatom _).resolve_left hCPlt.ne
    have hMst'mem : Mst' ∈ maximalSubgroupsContaining (Subgroup.centralizer (P : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨hco', hle'⟩
    have hMst'eq : Mst' = Mstar := by rw [hMstarCP] at hMst'mem; exact hMst'mem
    have hzMstar : z ∈ Mstar := hMst'eq ▸ hle' hzCP
    -- Theorem 12.5(e) for the original `(M, q, A)`: `M_σ ⊓ M* = ⊥` (since `M* ∈ ℳ(A)`, `M* ≠ M`).
    have h125e : S10.Msigma M ⊓ Mstar = ⊥ :=
      (Msigma_nilpotent_of_tau2 hG h.mem_maximal hq hA hAM).2.2.2.2.1 Mstar
        (mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hAMstar⟩) hMstarneM
    -- contradiction: `z ∈ M_σ ⊓ M* = ⊥` but `z ≠ 1`.
    exact hzne (by
      have : z ∈ S10.Msigma M ⊓ Mstar := Subgroup.mem_inf.mpr ⟨hzMσ, hzMstar⟩
      rwa [h125e, Subgroup.mem_bot] at this)

/-- **BG Lemma 13.13** (mmd L3765): if `p ∈ τ₁(M) ∪ τ₃(M)`, `P ∈ ℰ_p¹(E)`, and `C_{M_σ}(P) ≠ 1`,
then `p ∈ σ(M*)` for every `M* ∈ 𝓜(N_G(P))`.

Proof (BG L3767): by Lemma 12.2, `p ∈ σ(M*) ∪ τ₂(M*)`; suppose `p ∈ τ₂(M*)`.  Pick
`q ∈ π(C_{M_σ}(P))`, `Q ∈ ℰ_q¹(C_{M_σ}(P))`; by Theorem 13.9, `q ∉ σ(M*)`.  Let `E*` be a
complement of `M*_σ` in `M*` containing `PQ`, and `A ∈ ℰ_p²(E*)`; by Corollary 12.6(a), `A ◁ E*`
and `P ⊆ A`.  WLOG `P ≤ E₁` or `P ≤ E₃` (using Corollary 13.11 when `P ⊆ E₃`); Lemma 13.6 gives
`C_G(Q) ⊆ M`, so `A ⊄ C_{E*}(Q)` (as `r_p(M) = 1`), whence `q ∈ τ₁(M*)` by Corollary 12.10(c) and
`P = C_A(Q)`.  Lemma 13.12 for `M*` gives `C_{M*_σ}(Q) = 1`, and Corollary 12.9(c) then yields
`N_G(P) ⊄ M*`, contradicting `M* ∈ 𝓜(N_G(P))`.

Statement draft = Lane H (issue 2006); proof = Lane F (uses Lemma 13.12, 順序注意). -/
theorem mem_sigma_of_tau1_tau3_centralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p ∈ tau1 M ∪ tau3 M)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hCP : S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥)
    {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G))) :
    p ∈ S10.sigma Mstar := by
  sorry


end OddOrder.BG.Ch3.S13
