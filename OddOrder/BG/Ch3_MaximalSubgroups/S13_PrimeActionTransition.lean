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
    {p q : ℕ} (hp : p ∈ tau1 M) (hq : q ∈ tau2 M)
    {P A : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hA : A ∈ elemAbelianOfRank G q 2) (hAE : A ≤ E)
    (hCAP : A ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  sorry

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
