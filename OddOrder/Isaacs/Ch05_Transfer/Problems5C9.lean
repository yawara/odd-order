/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch05_Transfer.Problems5C8

/-!
# Isaacs Problem 5C.9 — 非可換単純・偶数位数・`8 ∤ |G|` なら `3 ∣ |G|` (p. 163)

**証明**: Sylow 2-部分群 `P` は位数 `2^n` (`1 ≤ n ≤ 2`) ゆえ可換。`3 ∤ |G|` と仮定すると
`N_G(P) ≤ C_G(P)` が出る: `|N_G(P) : C_G(P)|` は `|Aut P|` と `|G|` の両方を割り,
`P` 可換ゆえ奇数。素数 `q` がこれを割れば `exists_dvd_pow_sub_one_of_dvd_card_mulAut`
(Problem 5C.8 の軌道数え上げ補題) より `q ∣ 2^m - 1` (`1 ≤ m ≤ 2`) で,
`m = 1` なら `q ∣ 1`, `m = 2` なら `q = 3` — どちらも矛盾。

したがって Burnside で正規 2-補群 `K` が取れる。`G` 単純ゆえ `K = ⊥` または `K = ⊤`。
`K = ⊤` なら `|P| = 1` で `2 ∣ |G|` に反し, `K = ⊥` なら `P = ⊤` で `G` が可換になって
非可換性に反する。

⚠ 書籍は `Aut(C₂ × C₂) ≅ S₃` (位数 6) を使うが, ここでは 5C.8 と共通の軌道数え上げ補題で
`|Aut P|` を計算せずに済ませている。
-/

namespace OddOrder.Isaacs.Ch05

variable {G : Type*} [Group G]

section /- 5C.9: 非可換単純と `8 ∤ |G|` (p. 163) -/

/-- ⭐ **Isaacs Problem 5C.9** (p. 163): `G` が非可換単純で `|G|` が偶数, `8 ∤ |G|` なら
`3 ∣ |G|`。 -/
theorem three_dvd_card_of_isSimpleGroup_of_not_dvd_eight [Finite G] [IsSimpleGroup G]
    (hnonab : ¬ IsMulCommutative G) (h2 : 2 ∣ Nat.card G) (h8 : ¬ (8 : ℕ) ∣ Nat.card G) :
    3 ∣ Nat.card G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h3
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 G))
  obtain ⟨n, hn⟩ := P.2.exists_card_eq
  have hPdvd : Nat.card ↥(P : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hn2 : n ≤ 2 := by
    by_contra hc
    refine h8 ?_
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact dvd_trans (pow_dvd_pow 2 (by omega)) (hn ▸ hPdvd)
  have hn1 : 1 ≤ n := by
    by_contra hc
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hn
    have hidx : (P : Subgroup G).index = Nat.card G := by
      have hmul := Subgroup.card_mul_index (P : Subgroup G)
      rw [hn, one_mul] at hmul
      exact hmul
    exact P.not_dvd_index (hidx ▸ h2)
  -- `P` は可換 (位数 2 か 4)
  have hPab : IsMulCommutative ↥(P : Subgroup G) := by
    interval_cases n
    · have : IsCyclic ↥(P : Subgroup G) :=
        isCyclic_of_prime_card (p := 2) (by simpa using hn)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hn
  -- `N_G(P) ≤ C_G(P)`
  have hNC : Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    have key := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective (P : Subgroup G).normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex] at key
    refine Subgroup.relIndex_eq_one.mp ?_
    by_contra hne
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
    have hrelG : (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (P : Subgroup G)) ∣ Nat.card G :=
      dvd_trans (Subgroup.relIndex_dvd_card _ _) (Subgroup.card_subgroup_dvd_card _)
    have hqG : q ∣ Nat.card G := hqdvd.trans hrelG
    -- `2 ∤ |N : C|` (`P` 可換ゆえ `P ≤ C_G(P)`)
    have hpnot : ¬ (2 : ℕ) ∣ (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (P : Subgroup G)) := by
      intro hc
      have h1 : (Subgroup.centralizer ((P : Subgroup G) : Set G)).relIndex
          (Subgroup.normalizer (P : Subgroup G)) ∣
          (P : Subgroup G).relIndex (Subgroup.normalizer (P : Subgroup G)) :=
        Subgroup.relIndex_dvd_of_le_left _ P.le_centralizer
      have h2' : (P : Subgroup G).relIndex (Subgroup.normalizer (P : Subgroup G)) ∣
          (P : Subgroup G).index :=
        Subgroup.relIndex_dvd_index_of_le P.le_normalizer
      exact P.not_dvd_index ((hc.trans h1).trans h2')
    have hq2 : q ≠ 2 := fun hqe => hpnot (hqe ▸ hqdvd)
    obtain ⟨m, hm1, hmn, hq1⟩ :=
      exists_dvd_pow_sub_one_of_dvd_card_mulAut Nat.prime_two hn hq hq2 (hqdvd.trans key)
    have hm2 : m ≤ 2 := by omega
    interval_cases m
    · norm_num at hq1
      exact hq.one_lt.ne' hq1
    · norm_num at hq1
      exact h3 (((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hq1) ▸ hqG)
  -- Burnside による正規 2-補群と単純性
  obtain ⟨K, hKnormal, hKcompl⟩ :=
    hasNormalPComplement_of_sylow_normalizer_le_centralizer P hNC
  have hcard := (hKcompl P).card_mul_card
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K hKnormal with hbot | htop
  · -- `K = ⊥` ⇒ `P = ⊤` ⇒ `G` 可換 (非可換性に矛盾)
    rw [hbot, Subgroup.card_bot, one_mul] at hcard
    have hPtop : (P : Subgroup G) = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
    refine absurd (IsMulCommutative.of_comm fun a b => ?_) hnonab
    have hmem : ∀ x : G, x ∈ (P : Subgroup G) := fun x => hPtop ▸ Subgroup.mem_top x
    exact congrArg Subtype.val
      (mul_comm' (⟨a, hmem a⟩ : ↥(P : Subgroup G)) ⟨b, hmem b⟩)
  · -- `K = ⊤` ⇒ `|P| = 1` ⇒ `n = 0` (`1 ≤ n` に矛盾)
    rw [htop, Subgroup.card_top] at hcard
    have hP1 : Nat.card ↥(P : Subgroup G) = 1 :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [hcard, mul_one])
    rw [hn] at hP1
    rcases Nat.pow_eq_one.mp hP1 with h | h <;> omega

end

end OddOrder.Isaacs.Ch05
