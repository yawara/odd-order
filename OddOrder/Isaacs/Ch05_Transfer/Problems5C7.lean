/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.NormNum.Prime
import OddOrder.GroupTheory.CyclicSylowBurnside
import OddOrder.Isaacs.Ch05_Transfer.Problems5C4

/-!
# Isaacs Problem 5C.7 — `|G| = 3^a · 5 · 11` なら Sylow-3 は正規 (p. 163)

**証明** (Burnside の正規 `p`-補群定理を 2 段):

1. Sylow 5-部分群は位数 5 (巡回) で `φ(5) = 4` は `|G|` (奇数) と互いに素なので
   `N_G(P₅) = C_G(P₅)`。Burnside より `G` は正規 5-補群 `K` (位数 `3^a · 11`) を持つ。
2. `K` の Sylow 11-部分群は位数 11 (巡回) で `φ(11) = 10` は `|K| = 3^a · 11` と互いに素
   なので、同様に `K` は正規 11-補群 `L` (位数 `3^a`) を持つ。
3. `L` は `K` の正規 Sylow 3-部分群ゆえ特性部分群、`K ⊴ G` なので `L ⊴ G`。
   位数が `3^a` = `G` の Sylow-3 の位数なので `L` 自身が Sylow-3 であり、
   正規 Sylow は一意 (`Sylow.unique_of_normal`) だから任意の Sylow-3 が正規。

⚠ mathlib の `IsCyclic.normalizer_le_centralizer` は `p` が最小素因数のときしか使えない
(ここでは `p = 5, 11` で最小ではない) ので、一般形
`OddOrder.GroupTheory.normalizer_le_centralizer_of_coprime_totient` (issue 9210) を使う。
-/

namespace OddOrder.Isaacs.Ch05

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

section /- 5C.7: `|G| = 3^a · 5 · 11` (p. 163) -/

/-- `q` 素数で `q ∣ |G|` かつ `q^2 ∤ |G|` なら Sylow `q`-部分群の位数は `q`。 -/
theorem card_sylow_eq_self_of_sq_not_dvd {q : ℕ} [Fact q.Prime] [Finite G] (Q : Sylow q G)
    (h1 : q ∣ Nat.card G) (h2 : ¬ q ^ 2 ∣ Nat.card G) :
    Nat.card ↥(Q : Subgroup G) = q := by
  rw [Q.card_eq_multiplicity]
  have hne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hle : 1 ≤ (Nat.card G).factorization q := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out hne, pow_one]
    exact h1
  have hlt : (Nat.card G).factorization q < 2 := by
    by_contra hc
    exact h2 ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out hne).mpr (not_lt.mp hc))
  have heq : (Nat.card G).factorization q = 1 := by omega
  rw [heq, pow_one]

/-- `3 ∤ n` なら `(3^a · n).factorization 3 = a`。 -/
theorem factorization_three_pow_mul {a n : ℕ} (hn : n ≠ 0) (h3 : ¬ (3 : ℕ) ∣ n) :
    (3 ^ a * n).factorization 3 = a := by
  rw [Nat.factorization_mul (pow_ne_zero a (by norm_num)) hn, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd h3]
  simp

/-- `p` 素数, `p ∤ n` なら `p^2 ∤ p · n`。 -/
theorem sq_not_dvd_mul {p n : ℕ} (hp : p ≠ 0) (h : ¬ p ∣ n) : ¬ p ^ 2 ∣ p * n := by
  intro hc
  rw [pow_two] at hc
  exact h ((mul_dvd_mul_iff_left hp).mp hc)

/-- ⭐ **Isaacs Problem 5C.7** (p. 163): `|G| = 3^a · 5 · 11` なら `G` の Sylow 3-部分群は
正規。 -/
theorem normal_sylow_three_of_card_eq [Finite G] {a : ℕ}
    (hcard : Nat.card G = 3 ^ a * 5 * 11) (P : Sylow 3 G) : (P : Subgroup G).Normal := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hG55 : Nat.card G = 5 * (3 ^ a * 11) := by rw [hcard]; ring
  -- 段 1: 正規 5-補群 `K` (位数 `3^a · 11`)
  obtain ⟨P₅⟩ := (inferInstance : Nonempty (Sylow 5 G))
  have hP₅card : Nat.card ↥(P₅ : Subgroup G) = 5 := by
    refine card_sylow_eq_self_of_sq_not_dvd P₅ ⟨3 ^ a * 11, hG55⟩ ?_
    rw [hG55]
    refine sq_not_dvd_mul (by norm_num) ?_
    intro hc
    have hco : Nat.Coprime 5 (3 ^ a * 11) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_right a (by norm_num)) (by norm_num)
    exact absurd (Nat.eq_one_of_dvd_coprimes hco dvd_rfl hc) (by norm_num)
  have : IsCyclic ↥(P₅ : Subgroup G) := isCyclic_of_prime_card (p := 5) hP₅card
  have hcop5 : Nat.Coprime (Nat.card G) (Nat.totient (Nat.card ↥(P₅ : Subgroup G))) := by
    rw [hP₅card, hcard, show Nat.totient 5 = 4 from by decide]
    have h2 : Nat.Coprime (3 ^ a * 5 * 11) 2 :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_left
        (Nat.Coprime.pow_left a (by norm_num)) (by norm_num)) (by norm_num)
    have h4 := Nat.Coprime.pow_right 2 h2
    norm_num at h4
    exact h4
  obtain ⟨K, hKnormal, hKmul, -⟩ :=
    exists_normal_complement_of_isCyclic_sylow P₅ inferInstance hcop5
  have := hKnormal
  have hKcard : Nat.card ↥K = 3 ^ a * 11 := by
    rw [hP₅card] at hKmul
    rw [hG55] at hKmul
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 5 by norm_num) (by rw [hKmul]; ring)
  -- 段 2: `K` の正規 11-補群 `L` (位数 `3^a`)
  have hK11 : Nat.card ↥K = 11 * 3 ^ a := by rw [hKcard]; ring
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 11 ↥K))
  have hQcard : Nat.card ↥(Q : Subgroup ↥K) = 11 := by
    refine card_sylow_eq_self_of_sq_not_dvd Q ⟨3 ^ a, hK11⟩ ?_
    rw [hK11]
    refine sq_not_dvd_mul (by norm_num) ?_
    intro hc
    have hco : Nat.Coprime 11 (3 ^ a) := Nat.Coprime.pow_right a (by norm_num)
    exact absurd (Nat.eq_one_of_dvd_coprimes hco dvd_rfl hc) (by norm_num)
  have : IsCyclic ↥(Q : Subgroup ↥K) := isCyclic_of_prime_card (p := 11) hQcard
  have hcop11 : Nat.Coprime (Nat.card ↥K) (Nat.totient (Nat.card ↥(Q : Subgroup ↥K))) := by
    rw [hQcard, hKcard, show Nat.totient 11 = 10 from by decide,
      show (10 : ℕ) = 2 * 5 from by norm_num]
    exact Nat.Coprime.mul_right
      (Nat.Coprime.mul_left (Nat.Coprime.pow_left a (by norm_num)) (by norm_num))
      (Nat.Coprime.mul_left (Nat.Coprime.pow_left a (by norm_num)) (by norm_num))
  obtain ⟨L, hLnormal, hLmul, -⟩ :=
    exists_normal_complement_of_isCyclic_sylow Q inferInstance hcop11
  have := hLnormal
  have hLcard : Nat.card ↥L = 3 ^ a := by
    rw [hQcard, hK11] at hLmul
    exact Nat.eq_of_mul_eq_mul_right (show 0 < 11 by norm_num) (by rw [hLmul]; ring)
  -- 段 3: `L` は `K` の正規 Sylow-3 ⇒ 特性 ⇒ `L` を `G` へ押し出すと正規 Sylow-3
  have hfacK : (Nat.card ↥K).factorization 3 = a := by
    rw [hKcard]
    exact factorization_three_pow_mul (by norm_num) (by norm_num)
  let L' : Sylow 3 ↥K := Sylow.ofCard L (by rw [hLcard, hfacK])
  have hL'eq : (L' : Subgroup ↥K) = L := by simp [L']
  have : (L' : Subgroup ↥K).Normal := by rw [hL'eq]; exact hLnormal
  have : L.Characteristic := hL'eq ▸ Sylow.characteristic_of_normal L' inferInstance
  have : (L.map K.subtype).Normal := normal_map_subtype_of_characteristic
  have hmapcard : Nat.card ↥(L.map K.subtype) = 3 ^ a := by
    rw [← hLcard]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective L _ (Subgroup.subtype_injective _)).toEquiv.symm
  have hfacG : (Nat.card G).factorization 3 = a := by
    rw [hcard, show 3 ^ a * 5 * 11 = 3 ^ a * 55 by ring]
    exact factorization_three_pow_mul (by norm_num) (by norm_num)
  let P₀ : Sylow 3 G := Sylow.ofCard (L.map K.subtype) (by rw [hmapcard, hfacG])
  have hP₀eq : (P₀ : Subgroup G) = L.map K.subtype := by simp [P₀]
  have : (P₀ : Subgroup G).Normal := by rw [hP₀eq]; infer_instance
  have := Sylow.unique_of_normal P₀ inferInstance
  rw [Subsingleton.elim P P₀]
  infer_instance

end

end OddOrder.Isaacs.Ch05
