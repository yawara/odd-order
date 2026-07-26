/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.Isaacs.Ch05_Transfer.Problems5C8

/-!
# Isaacs Problem 5C.10 — 単純群の可換 Sylow-2 が位数 8 なら `7 ∣ |G|` (p. 164)

**証明**: `7 ∤ |G|` と仮定する。`G` 単純で `8 ∣ |G|` なので `G` は非可換, すなわち
`commutator G = ⊤`。Isaacs Thm 5.18 (`eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer`)
より `P ∩ Z(N_G(P)) ∩ G' = 1` だが `G' = G` なので **`C_P(N_G(P)) = 1`**。

一方 `S := N_G(P)/C_G(P)` (= `normalizerMonoidHom` の像) の位数を割る素数 `q` は
`P` 可換ゆえ奇数で, `Problems5C8` の軌道数え上げ補題より `q ∣ 2^m - 1` (`1 ≤ m ≤ 3`),
すなわち `q ∈ {3, 7}`。`7 ∤ |G|` から `q = 3` のみ, つまり `S` は 3-群。

`S` の `P` への作用の不動点は `C_P(N_G(P)) = 1` なので軌道数え上げ
(`IsPGroup.card_modEq_card_fixedPoints`) より `8 ≡ 1 (mod 3)`, これは偽。

⭐ この論法は `P` の同型類 (`C₈` / `C₄×C₂` / `C₂³`) を場合分けしない。`S` が自明な場合も
「不動点全体 = `P` が自明」となって同じ合同式で潰れる。
-/

namespace OddOrder.Isaacs.Ch05

open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 5C.10: 単純群と位数 8 の可換 Sylow-2 (p. 164) -/

/-- ⭐ **Isaacs Problem 5C.10** (p. 164): `G` が単純で位数 8 の可換 Sylow 2-部分群を持つなら
`7 ∣ |G|`。 -/
theorem seven_dvd_card_of_isSimpleGroup_of_card_sylow_two_eq_eight
    [Finite G] [IsSimpleGroup G] (P : Sylow 2 G)
    [hPab : IsMulCommutative ↥(P : Subgroup G)]
    (hcard : Nat.card ↥(P : Subgroup G) = 8) :
    7 ∣ Nat.card G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h7
  have hPdvd : Nat.card ↥(P : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have h8G : (8 : ℕ) ∣ Nat.card G := hcard ▸ hPdvd
  -- `G` は非可換単純ゆえ `G' = ⊤`
  have hcomm : _root_.commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator G) inferInstance with
      hbot | htop
    · exfalso
      have hab : ∀ x y : G, x * y = y * x := by
        intro x y
        have hmem : ⁅x, y⁆ ∈ _root_.commutator G := by
          rw [_root_.commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp hmem
      letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hab }
      have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
      rcases (Nat.Prime.eq_one_or_self_of_dvd hprime 8 h8G) with h | h
      · omega
      · exact absurd (h ▸ hprime) (by norm_num)
    · exact htop
  -- `C_P(N_G(P)) = 1` (Thm 5.18 + `G' = ⊤`)
  have hfix1 : ∀ x : ↥(P : Subgroup G),
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n * (x : G) = (x : G) * n) →
      x = 1 := by
    intro x hx
    refine Subtype.ext ?_
    exact eq_one_of_mem_commutator_of_mem_sylow_of_central_normalizer P
      (hcomm ▸ Subgroup.mem_top (x : G)) x.2 hx
  -- `S := N_G(P)/C_G(P)` は 3-群
  set f := Subgroup.normalizerMonoidHom (P : Subgroup G) with hf
  have hrangecard : Nat.card ↥f.range =
      (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (P : Subgroup G)) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hf,
      Subgroup.normalizerMonoidHom_ker]
    rfl
  have hrelG : (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (P : Subgroup G)) ∣ Nat.card G :=
    dvd_trans (Subgroup.relIndex_dvd_card _ _) (Subgroup.card_subgroup_dvd_card _)
  have hnot2 : ¬ (2 : ℕ) ∣ (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (P : Subgroup G)) := by
    intro hc
    have h1 : (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (P : Subgroup G)) ∣
        (P : Subgroup G).relIndex (Subgroup.normalizer (P : Subgroup G)) :=
      Subgroup.relIndex_dvd_of_le_left _ P.le_centralizer
    have h2 : (P : Subgroup G).relIndex (Subgroup.normalizer (P : Subgroup G)) ∣
        (P : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le P.le_normalizer
    exact P.not_dvd_index ((hc.trans h1).trans h2)
  have hqeq3 : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥f.range → q = 3 := by
    intro q hq hqdvd
    rw [hrangecard] at hqdvd
    have hq2 : q ≠ 2 := fun hqe => hnot2 (hqe ▸ hqdvd)
    have hqAut : q ∣ Nat.card (MulAut ↥(P : Subgroup G)) := by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card f.range)
      rw [hrangecard]
      exact hqdvd
    have hn3 : Nat.card ↥(P : Subgroup G) = 2 ^ 3 := by rw [hcard]; norm_num
    obtain ⟨m, hm1, hm3, hqm⟩ :=
      exists_dvd_pow_sub_one_of_dvd_card_mulAut Nat.prime_two hn3 hq hq2 hqAut
    interval_cases m
    · norm_num at hqm
      exact absurd hqm hq.one_lt.ne'
    · norm_num at hqm
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hqm
    · norm_num at hqm
      exact absurd (((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqm) ▸
        (hqdvd.trans hrelG)) h7
  have hSp : IsPGroup 3 ↥f.range := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hdvd : orderOf g ∣ Nat.card ↥f.range := orderOf_dvd_natCard g
    exact ⟨(orderOf g).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos g).ne'
        fun {q} hq hqo => hqeq3 q hq (hqo.trans hdvd)⟩
  -- 軌道数え上げ: `|P| ≡ |Fix| (mod 3)` で `|Fix| = 1`
  have hfixtriv : MulAction.fixedPoints ↥f.range ↥(P : Subgroup G) = {1} := by
    ext x
    constructor
    · intro hx
      refine Set.mem_singleton_iff.mpr (hfix1 x ?_)
      intro n hn
      have hxfix := hx ⟨f ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩⟩
      have hval : (n * (x : G) * n⁻¹) = (x : G) := congrArg Subtype.val hxfix
      calc n * (x : G) = n * (x : G) * n⁻¹ * n := by group
        _ = (x : G) * n := by rw [hval]
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      intro g
      exact map_one _
  have hmod := hSp.card_modEq_card_fixedPoints (α := ↥(P : Subgroup G))
  rw [hfixtriv, hcard] at hmod
  have hone : Nat.card ({1} : Set ↥(P : Subgroup G)) = 1 := by simp
  rw [hone] at hmod
  have : (3 : ℕ) ∣ 7 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
  omega

end

end OddOrder.Isaacs.Ch05
