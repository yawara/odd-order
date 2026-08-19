/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6B1
import OddOrder.Isaacs.Ch03_SplitExtensions.Main

/-!
# Isaacs Problem 6B.9 — 可解 EPPO 群の素因数は高々 2 個 (書籍 p. 196)

**主張**: 可解群 `G` の全ての元が素数冪位数をもつなら, `|G|` を割る素数は高々 2 個。

**証明の筋** (素数が 3 個以上あると仮定して矛盾):

1. `G` の minimal normal subgroup `U` は elementary abelian `p`-群 (Isaacs Thm 3.11)。
2. `p` 以外に 2 つの素数 `q ≠ r` が `|G|` を割る。可解性から Hall `{p}ᶜ`-部分群 `K` が
   存在し (Isaacs Thm 3.13), `q, r ∣ |K|` かつ `p ∤ |K|`。
3. EPPO ゆえ**位数が互いに素な非自明元は可換になれない** (可換なら積の位数が相異なる
   2 素数で割れて素数冪でない)。とくに `K` の共役作用は `U` 上 **Frobenius**。
4. `K` の minimal normal subgroup `M` は elementary abelian `s`-群。`{q, r}` のうち `s` と
   異なる素数 `t` を取り `y ∈ K` を位数 `t` に取ると, `M⟨y⟩` は Frobenius 群
   (核 `M`, 素数位数の補群 `⟨y⟩`; 固定点自由性は EPPO から)。
5. Frobenius 補群は Frobenius 群を部分群に持てない (Isaacs Thm 6.9 の可解分岐,
   6B.1 の "deduce" 部分) ので矛盾。
-/

namespace OddOrder.Isaacs.Ch06

section /- 6B.9: 可解 EPPO 群 (p. 196) -/

/-- **EPPO の要**: 全元が素数冪位数の群では, 位数が互いに素な非自明元は可換になれない。

可換なら `orderOf (x * y) = orderOf x * orderOf y` が相異なる 2 素数で割れてしまう。 -/
theorem false_of_commute_of_coprime_orderOf {G : Type*} [Group G] [Finite G]
    (hEPPO : ∀ g : G, ∃ t : ℕ, t.Prime ∧ ∃ k : ℕ, orderOf g = t ^ k)
    {x y : G} (hx : x ≠ 1) (hy : y ≠ 1)
    (hcop : Nat.Coprime (orderOf x) (orderOf y)) (hcomm : x * y = y * x) : False := by
  have hmul : orderOf (x * y) = orderOf x * orderOf y :=
    (Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm hcop)
  obtain ⟨t, ht, k, hk⟩ := hEPPO (x * y)
  have hxne : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  have hyne : orderOf y ≠ 1 := fun h => hy (orderOf_eq_one_iff.mp h)
  have hxdvd : orderOf x ∣ t ^ k := by rw [← hk, hmul]; exact dvd_mul_right _ _
  have hydvd : orderOf y ∣ t ^ k := by rw [← hk, hmul]; exact dvd_mul_left _ _
  obtain ⟨u, hu, hux⟩ := Nat.exists_prime_and_dvd hxne
  obtain ⟨v, hv, hvy⟩ := Nat.exists_prime_and_dvd hyne
  have hut : u = t := (Nat.prime_dvd_prime_iff_eq hu ht).mp (hu.dvd_of_dvd_pow (hux.trans hxdvd))
  have hvt : v = t := (Nat.prime_dvd_prime_iff_eq hv ht).mp (hv.dvd_of_dvd_pow (hvy.trans hydvd))
  have hdvd1 : t ∣ 1 := hcop ▸ Nat.dvd_gcd (hut ▸ hux) (hvt ▸ hvy)
  exact ht.one_lt.ne' (Nat.dvd_one.mp hdvd1)

/-- 部分群版: 位数が互いに素な 2 つの部分群の非自明元は, EPPO 群では可換になれない。 -/
theorem false_of_commute_of_coprime_card {G : Type*} [Group G] [Finite G]
    (hEPPO : ∀ g : G, ∃ t : ℕ, t.Prime ∧ ∃ k : ℕ, orderOf g = t ^ k)
    {H K : Subgroup G} (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥K))
    {x y : G} (hxH : x ∈ H) (hyK : y ∈ K) (hx : x ≠ 1) (hy : y ≠ 1)
    (hcomm : x * y = y * x) : False := by
  refine false_of_commute_of_coprime_orderOf hEPPO hx hy ?_ hcomm
  have hxdvd : orderOf x ∣ Nat.card ↥H := by
    have h := orderOf_dvd_natCard (⟨x, hxH⟩ : ↥H)
    rwa [← Subgroup.orderOf_coe] at h
  have hydvd : orderOf y ∣ Nat.card ↥K := by
    have h := orderOf_dvd_natCard (⟨y, hyK⟩ : ↥K)
    rwa [← Subgroup.orderOf_coe] at h
  exact Nat.Coprime.coprime_dvd_left hxdvd (Nat.Coprime.coprime_dvd_right hydvd hcop)

/-- **Frobenius 群の作り方**: 非自明な `M` を素数位数 `t` の `y` が正規化し,
`|M|` と `t` が互いに素で `M` の非自明元が `y` に固定されないなら, `M⟨y⟩` は
核 `M`・補群 `⟨y⟩` の Frobenius 群。

6B.1 前半 (`exists_isSolvable_isFrobeniusGroup_of_isFrobeniusGroup`) の構成を
仮説だけ抽象化して切り出したもの。 -/
theorem isFrobeniusGroup_sup_zpowers_of_prime_orderOf {G : Type*} [Group G] [Finite G]
    {M : Subgroup G} (hMne : M ≠ ⊥)
    {y : G} {t : ℕ} (ht : t.Prime) (hy : orderOf y = t)
    (hnorm : y ∈ Subgroup.normalizer M) (hcop : Nat.Coprime (Nat.card ↥M) t)
    (hfree : ∀ n ∈ M, n ≠ 1 → y * n * y⁻¹ ≠ n) :
    IsFrobeniusGroup ↥(M ⊔ Subgroup.zpowers y)
      (M.subgroupOf (M ⊔ Subgroup.zpowers y))
      ((Subgroup.zpowers y).subgroupOf (M ⊔ Subgroup.zpowers y)) := by
  set Y : Subgroup G := Subgroup.zpowers y with hYdef
  set H : Subgroup G := M ⊔ Y with hHdef
  have hYnorm : Y ≤ Subgroup.normalizer M := Subgroup.zpowers_le.mpr hnorm
  have hYcard : Nat.card ↥Y = t := by rw [hYdef, Nat.card_zpowers, hy]
  have hcardH : Nat.card ↥H = Nat.card ↥M * Nat.card ↥Y :=
    card_sup_of_le_normalizer_of_coprime hYnorm (by rwa [hYcard])
  have hMH : M ≤ H := le_sup_left
  have hYH : Y ≤ H := le_sup_right
  have hcardMsub : Nat.card ↥(M.subgroupOf H) = Nat.card ↥M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv
  have hcardYsub : Nat.card ↥(Y.subgroupOf H) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  -- 位数の互素性から交わりは自明
  have hdisj : Disjoint (M.subgroupOf H) (Y.subgroupOf H) := by
    rw [disjoint_iff_inf_le]
    intro z hz
    have hzM : orderOf ((z : ↥H) : G) ∣ Nat.card ↥M := by
      have h := orderOf_dvd_natCard (⟨((z : ↥H) : G), hz.1⟩ : ↥M)
      rwa [← Subgroup.orderOf_coe] at h
    have hzY : orderOf ((z : ↥H) : G) ∣ t := by
      have h := orderOf_dvd_natCard (⟨((z : ↥H) : G), hz.2⟩ : ↥Y)
      rwa [← Subgroup.orderOf_coe, hYcard] at h
    have hone : orderOf ((z : ↥H) : G) = 1 := Nat.eq_one_of_dvd_coprimes hcop hzM hzY
    have : ((z : ↥H) : G) = 1 := orderOf_eq_one_iff.mp hone
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hcompl : Subgroup.IsComplement' (M.subgroupOf H) (Y.subgroupOf H) :=
    Subgroup.isComplement'_of_card_mul_and_disjoint
      (by rw [hcardMsub, hcardYsub, hcardH]) hdisj
  have hMnormal : (M.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgH : ((g : ↥H) : G) ∈ Subgroup.normalizer M :=
      (sup_le Subgroup.le_normalizer hYnorm : H ≤ Subgroup.normalizer M) g.2
    exact (Subgroup.mem_normalizer_iff.mp hgH ((n : ↥H) : G)).mp hn
  refine isFrobeniusGroup_of_prime_complement_fixedFree hcompl (by rw [hcardYsub, hYcard]; exact ht)
    ?_ ?_
  · refine (Subgroup.nontrivial_iff_ne_bot _).mp (Finite.one_lt_card_iff_nontrivial.mp ?_)
    rw [hcardMsub]
    exact Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot M).mpr hMne)
  · intro n hn hfix
    by_contra hne
    have hyH : y ∈ H := hYH (Subgroup.mem_zpowers y)
    have hfixy := hfix ⟨y, hyH⟩ (Subgroup.mem_zpowers y)
    refine hfree (n : G) hn (fun h => hne (Subtype.ext h)) ?_
    have h := congrArg (fun w : ↥H => (w : G)) hfixy
    simpa using h

/-- **Isaacs Problem 6B.9** (p. 196) ⭐: 可解群 `G` の全ての元が素数冪位数をもつなら
`|G|` の素因数は高々 2 個。 -/
theorem card_primeFactors_le_two_of_forall_prime_pow_orderOf {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable G] (hEPPO : ∀ g : G, ∃ t : ℕ, t.Prime ∧ ∃ k : ℕ, orderOf g = t ^ k) :
    (Nat.card G).primeFactors.card ≤ 2 := by
  classical
  by_contra hcon
  have h3 : 3 ≤ (Nat.card G).primeFactors.card := by omega
  -- (1) minimal normal subgroup `U` は elementary abelian `p`-群
  have hGne : (⊤ : Subgroup G) ≠ ⊥ := by
    intro htop
    have hcard : Nat.card G = 1 := by
      have : Nat.card ↥(⊤ : Subgroup G) = 1 := by rw [htop]; simp
      rwa [Subgroup.card_top] at this
    rw [hcard] at h3
    simp at h3
  obtain ⟨U, hUmin, -⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) hGne
  have hUnormal : U.Normal := hUmin.1
  have hUne : U ≠ ⊥ := hUmin.2.1
  have hUnt : Nontrivial ↥U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
  obtain ⟨p, hp, hUea⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hUmin
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨kU, hUcard⟩ := hUea.isPGroup.exists_card_eq
  -- (2) `p` 以外の 2 素数 `q ≠ r` と Hall `{p}ᶜ`-部分群 `K`
  have h2 : 1 < ((Nat.card G).primeFactors.erase p).card :=
    lt_of_lt_of_le (by omega) (Finset.pred_card_le_card_erase (a := p))
  obtain ⟨q, hqmem, r, hrmem, hqr⟩ := Finset.one_lt_card.mp h2
  have hqp : q ≠ p := (Finset.mem_erase.mp hqmem).1
  have hrp : r ≠ p := (Finset.mem_erase.mp hrmem).1
  have hqfac := Nat.mem_primeFactors.mp (Finset.mem_erase.mp hqmem).2
  have hrfac := Nat.mem_primeFactors.mp (Finset.mem_erase.mp hrmem).2
  obtain ⟨K, hK⟩ :=
    OddOrder.Isaacs.Ch03.hall_exists_of_piSeparable (G := G) {u : ℕ | u ≠ p}
  have hdvdK : ∀ u : ℕ, u.Prime → u ≠ p → u ∣ Nat.card G → u ∣ Nat.card ↥K := by
    intro u hu hup hudvd
    have hsplit : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
    rcases (Nat.Prime.dvd_mul hu).mp (hsplit ▸ hudvd) with h | h
    · exact h
    · exact absurd (hK.2 u (Nat.mem_primeFactors.mpr
        ⟨hu, h, Subgroup.index_ne_zero_of_finite⟩)) (by simpa using hup)
  have hpK : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    exact absurd (hK.1 p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)) (by simp)
  have hcopKU : Nat.Coprime (Nat.card ↥K) (Nat.card ↥U) := by
    rw [hUcard]
    exact (((hp.coprime_iff_not_dvd).mpr hpK).symm).pow_right kU
  have hqK : q ∣ Nat.card ↥K := hdvdK q hqfac.1 hqp hqfac.2.1
  have hrK : r ∣ Nat.card ↥K := hdvdK r hrfac.1 hrp hrfac.2.1
  -- (3) `K` の共役作用は `U` 上 Frobenius
  let actK : MulDistribMulAction ↥K ↥U :=
    MulDistribMulAction.compHom ↥U ((MulAut.conjNormal (H := U)).comp K.subtype)
  have hFrobAct : IsFrobeniusAction ↥K ↥U := by
    intro a ha n hn hfix
    have haG : ((a : ↥K) : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hnG : ((n : ↥U) : G) ≠ 1 := fun h => hn (Subtype.ext h)
    have hfixG : ((a : ↥K) : G) * ((n : ↥U) : G) * ((a : ↥K) : G)⁻¹ = ((n : ↥U) : G) :=
      Subtype.ext_iff.mp hfix
    have hcomm : ((a : ↥K) : G) * ((n : ↥U) : G) = ((n : ↥U) : G) * ((a : ↥K) : G) := by
      have h := congrArg (· * ((a : ↥K) : G)) hfixG
      simpa [mul_assoc] using h
    exact false_of_commute_of_coprime_card hEPPO hcopKU a.2 n.2 haG hnG hcomm
  -- (4) `K` の minimal normal subgroup `M` と位数 `t` の元 `y` で Frobenius 部分群を作る
  have hEPPOK : ∀ g : ↥K, ∃ t : ℕ, t.Prime ∧ ∃ k : ℕ, orderOf g = t ^ k := by
    intro g
    obtain ⟨t, ht, k, hk⟩ := hEPPO ((g : ↥K) : G)
    exact ⟨t, ht, k, by rwa [Subgroup.orderOf_coe] at hk⟩
  have hKne : (⊤ : Subgroup ↥K) ≠ ⊥ := by
    intro htop
    have hcard : Nat.card ↥K = 1 := by
      have : Nat.card ↥(⊤ : Subgroup ↥K) = 1 := by rw [htop]; simp
      rwa [Subgroup.card_top] at this
    rw [hcard] at hqK
    exact hqfac.1.one_lt.ne' (Nat.dvd_one.mp hqK)
  obtain ⟨M, hMmin, -⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup ↥K) hKne
  have hMnormal : M.Normal := hMmin.1
  have hMne : M ≠ ⊥ := hMmin.2.1
  obtain ⟨s, hs, hMea⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hMmin
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨kM, hMcard⟩ := hMea.isPGroup.exists_card_eq
  -- `{q, r}` のうち `s` と異なるものを `t` に取る
  obtain ⟨t, ht, htK, hts⟩ : ∃ t : ℕ, t.Prime ∧ t ∣ Nat.card ↥K ∧ t ≠ s := by
    rcases eq_or_ne q s with hqs | hqs
    · exact ⟨r, hrfac.1, hrK, fun h => hqr (hqs.trans h.symm)⟩
    · exact ⟨q, hqfac.1, hqK, hqs⟩
  have : Fact t.Prime := ⟨ht⟩
  have : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card (G := ↥K) t
    (by rwa [← Nat.card_eq_fintype_card])
  -- `M⟨y⟩` は Frobenius 群
  have hcopM : Nat.Coprime (Nat.card ↥M) t := by
    rw [hMcard]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hs ht).mpr (Ne.symm hts))
  have hy1 : y ≠ 1 := by
    intro h
    have h1 : orderOf y = 1 := orderOf_eq_one_iff.mpr h
    rw [hyord] at h1
    exact ht.one_lt.ne' h1
  have hfree : ∀ n ∈ M, n ≠ 1 → y * n * y⁻¹ ≠ n := by
    intro n hn hne hfix
    have hns : orderOf n ∣ s := by
      have h := hMea.pow_eq_one ⟨n, hn⟩
      exact orderOf_dvd_of_pow_eq_one (congrArg Subtype.val h)
    have hcomm : n * y = y * n := by
      have h := congrArg (· * y) hfix
      simpa [mul_assoc] using h.symm
    refine false_of_commute_of_coprime_orderOf hEPPOK hne hy1 ?_ hcomm
    refine Nat.Coprime.coprime_dvd_left hns ?_
    rw [hyord]
    exact (Nat.coprime_primes hs ht).mpr (Ne.symm hts)
  have hynorm : y ∈ Subgroup.normalizer M := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hMnormal]
    exact Subgroup.mem_top y
  have hFrobB :=
    isFrobeniusGroup_sup_zpowers_of_prime_orderOf hMne ht hyord hynorm hcopM hfree
  -- (5) Frobenius 補群は Frobenius 群を含めない (Thm 6.9 可解分岐)
  have : Group.IsSolvable ↥(M ⊔ Subgroup.zpowers y) :=
    Group.isSolvable_of_isSolvable_injective (f := (M ⊔ Subgroup.zpowers y).subtype)
      (Subgroup.subtype_injective _)
  exact false_of_frobeniusAction_actorSubgroup_isSolvable_isFrobeniusGroup hFrobAct
    (M ⊔ Subgroup.zpowers y) hFrobB

end

end OddOrder.Isaacs.Ch06
