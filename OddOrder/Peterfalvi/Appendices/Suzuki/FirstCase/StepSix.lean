/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepFive

/-!
# Peterfalvi Part II, Ch. II, step (6): the arithmetic lemma

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (6), p. 110.

Step (6) rests on a number-theoretic lemma quoted from Huppert–Blackburn
([HB], Kapitel IX, Lemma 2.7): the only way an odd prime power `f^a` can equal
`2^b + 1` is `a = 1` (so `f = 2^b + 1` is a Fermat prime) or `f^a = 9`
(`3² = 2³ + 1`).

This leaf formalizes that lemma as `eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one`
(pure `ℕ` arithmetic, axiom-clean).  The elementary proof:

* if `a ≥ 2`, the geometric sum `S = ∑_{i<a} f^i` divides `2^b` (as
  `(f - 1) · S = f^a - 1 = 2^b`), so `S` is a power of `2`; but `S ≡ a (mod 2)`
  (each `f^i` is odd), and `S ≥ 1 + f ≥ 4` is even, forcing `a` even;
* writing `a = 2c`, `(f^c - 1)(f^c + 1) = 2^b`, so both factors are powers of
  `2` differing by `2`, hence `2` and `4`; thus `f^c = 3` and `f^a = 9`.

The lemma is consumed by step (6) (`|F| = f^a = 2^b + 1`) and step (8)
(`|C_F(w)| = f^a = 2^b + 1`).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open Finset

/-- **[HB] Kapitel IX, Lemma 2.7** (arithmetic): if `f` is odd and
`f ^ a = 2 ^ b + 1` with `b ≥ 1`, then `a = 1` or `f ^ a = 9`.

Consumed by step (6) and step (8) of Peterfalvi Part II, Ch. II. -/
theorem eq_one_or_pow_eq_nine_of_pow_eq_two_pow_add_one {f a b : ℕ}
    (hf : Odd f) (hb : 1 ≤ b) (h : f ^ a = 2 ^ b + 1) :
    a = 1 ∨ f ^ a = 9 := by
  have hfodd := Nat.odd_iff.mp hf
  have hb2 : 2 ≤ 2 ^ b := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  -- `f ≥ 3`
  have hf3 : 3 ≤ f := by
    rcases Nat.lt_or_ge f 3 with hlt | hge
    · exfalso
      have hf1 : f = 1 := by omega
      rw [hf1, one_pow] at h
      omega
    · exact hge
  -- `a ≥ 1`
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [pow_zero] at h; omega
    · exact hpos
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · left; omega
  right
  -- `a ≥ 2`.  The geometric sum `S = ∑_{i<a} f^i`.
  set S : ℕ := ∑ i ∈ Finset.range a, f ^ i with hSdef
  -- `(f - 1) · S = f^a - 1 = 2^b`
  have hgeom : (f - 1) * S = f ^ a - 1 := by
    rw [hSdef, Nat.geomSum_eq (by omega) a]
    exact Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one f a)
  have hprod : (f - 1) * S = 2 ^ b := by rw [hgeom]; omega
  have hSdvd : S ∣ 2 ^ b := ⟨f - 1, by rw [← hprod]; ring⟩
  obtain ⟨k, -, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hSdvd
  -- `S ≡ a (mod 2)`
  have hSpar : S % 2 = a % 2 := by
    rw [hSdef, Finset.sum_nat_mod]
    have hone : ∀ i ∈ Finset.range a, f ^ i % 2 = 1 :=
      fun i _ => Nat.odd_iff.mp hf.pow
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  -- `S ≥ 1 + f ≥ 4`, so `S` is even, hence `a` is even
  have hSge : 4 ≤ S := by
    have hsub : Finset.range 2 ⊆ Finset.range a := by
      intro x hx; rw [Finset.mem_range] at hx ⊢; omega
    have hle : ∑ i ∈ Finset.range 2, f ^ i ≤ S :=
      hSdef ▸ Finset.sum_le_sum_of_subset hsub
    have h2 : ∑ i ∈ Finset.range 2, f ^ i = 1 + f := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
    rw [h2] at hle; omega
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero] at hSk; omega
    · exact hkpos
  have hSeven : 2 ∣ S := hSk ▸ dvd_pow_self 2 (by omega)
  have haeven : 2 ∣ a := by
    have : a % 2 = 0 := by omega
    omega
  obtain ⟨c, rfl⟩ := haeven
  have hcpos : 1 ≤ c := by omega
  -- `g = f^c ≥ 3`, and `(g - 1)(g + 1) = 2^b`
  set g : ℕ := f ^ c with hgdef
  have hgge : 3 ≤ g := by
    calc 3 ≤ f := hf3
      _ = f ^ 1 := (pow_one f).symm
      _ ≤ f ^ c := Nat.pow_le_pow_right (by omega) hcpos
  have hg2 : g ^ 2 = 2 ^ b + 1 := by
    rw [hgdef, ← pow_mul, mul_comm c 2]; exact h
  have hfactor : (g - 1) * (g + 1) = 2 ^ b := by
    have hge1 : 1 ≤ g := by omega
    zify [hge1]
    have : (g : ℤ) ^ 2 = 2 ^ b + 1 := by exact_mod_cast hg2
    linear_combination this
  -- both factors are powers of `2`, differing by `2`
  have hgm1 : (g - 1) ∣ 2 ^ b := ⟨g + 1, hfactor.symm⟩
  have hgp1 : (g + 1) ∣ 2 ^ b := ⟨g - 1, by rw [mul_comm]; exact hfactor.symm⟩
  obtain ⟨u, -, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgm1
  obtain ⟨v, -, hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgp1
  -- `2^v = 2^u + 2` with `u ≥ 1`, forcing `u = 1`, i.e. `g = 3`
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · rw [pow_zero] at hu; omega
    · exact hupos
  have huv : u < v := by
    have : (2 : ℕ) ^ u < 2 ^ v := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hudvd : (2 : ℕ) ^ u ∣ 2 := by
    have h1 : (2 : ℕ) ^ u ∣ 2 ^ v := pow_dvd_pow 2 huv.le
    have hveq : (2 : ℕ) ^ v = 2 ^ u + 2 := by omega
    rw [hveq] at h1
    exact (Nat.dvd_add_right (dvd_refl _)).mp h1
  have hule : (2 : ℕ) ^ u = 2 := by
    have hle := Nat.le_of_dvd (by norm_num) hudvd
    have hge : 2 ≤ (2 : ℕ) ^ u := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu1
    omega
  have hg3 : g = 3 := by omega
  -- `f^a = f^(2c) = (f^c)^2 = g^2 = 9`
  rw [mul_comm 2 c, pow_mul, ← hgdef, hg3]
  norm_num
