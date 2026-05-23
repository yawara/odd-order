/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.SetTheory.Cardinal.Finite

/-!
# OddOrder.Isaacs.Ch06 — Frobenius Actions

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 6
"Frobenius Actions" (pp. 177-200) の Lean 化.

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 6A | Frobenius action の定義と equivalences | 6.1 – 6.7 | 進行中: 6.1 ✅, 6.3-6.6 未, 6.2/6.7 保留 |
| 6B | Frobenius complement Sylow 構造 | 6.8 – 6.21 | 未着手 |
| 6C | Frobenius kernel nilpotent + Thompson | 6.22 – 6.24 | 未着手 |

## 方針

mathlib カバレッジ薄 (~21%; `DihedralGroup`/`QuaternionGroup` の具体群以外は新規実装).
**`FrobeniusGroup` / `FrobeniusAction` は mathlib 完全未収載** — 本ファイルで一次定義.

設計: Isaacs 本文に従い **action ベース** (`IsFrobeniusAction A N` on `MulDistribMulAction A N`) を
中核に置き, subgroup-pair 版 (`IsFrobeniusGroup G N A`) は conjugation action で導出.

## 先行章依存

本ファイル §6A の本実装範囲 (6.1, 6.3, 6.4, 6.5, 6.6) は **Isaacs 先行章への依存なし**.
6.2 (Cor 3.28) と 6.7 (Schur-Zassenhaus) は Ch.3 完成後 / mathlib SZ 経由で別 commit.

ノート: [`notes/isaacs/ch06_frobenius_actions.md`](../../notes/isaacs/ch06_frobenius_actions.md)
-/

namespace OddOrder.Isaacs.Ch06

section /- 6A: Frobenius action basics (pp. 177-183) -/

/-! ### Definition of Frobenius action

Isaacs Defn (p. 177): an action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity
element of `A` fixes any nonidentity element of `N`. Equivalently `C_N(a) = 1` for all `1 ≠ a ∈ A`,
or `C_A(n) = 1` for all `1 ≠ n ∈ N`, or the action of `A` on `N \ {1}` is semiregular. -/

/-- An action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity element of `A`
fixes any nonidentity element of `N`.

Isaacs p. 177: "the action of `A` on `N` is said to be Frobenius if `n^a ≠ n` whenever `n ∈ N`
and `a ∈ A` are nonidentity elements." -/
def IsFrobeniusAction (A N : Type*) [Group A] [Group N] [MulDistribMulAction A N] : Prop :=
  ∀ a : A, a ≠ 1 → ∀ n : N, n ≠ 1 → a • n ≠ n

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

namespace IsFrobeniusAction

/-- The orbit of `1 ∈ N` under any `MulDistribMulAction` is `{1}`. (Structural, not Frobenius.) -/
theorem orbit_one : MulAction.orbit A (1 : N) = {1} := by
  ext n
  simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩; exact smul_one a
  · rintro rfl; exact ⟨1, smul_one 1⟩

/-- **Frobenius action ⇒ stabilizer trivial on nonidentity.** -/
theorem stabilizer_eq_bot (h : IsFrobeniusAction A N) {n : N} (hn : n ≠ 1) :
    MulAction.stabilizer A n = ⊥ := by
  ext a
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  refine ⟨fun hax => ?_, ?_⟩
  · by_contra ha; exact h a ha n hn hax
  · rintro rfl; exact one_smul A n

/-- **Frobenius action: `fixedBy N a = {1}` for `a ≠ 1`.** -/
theorem fixedBy_eq_singleton_one (h : IsFrobeniusAction A N) {a : A} (ha : a ≠ 1) :
    MulAction.fixedBy N a = {1} := by
  ext n
  simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
  refine ⟨fun hn => ?_, ?_⟩
  · by_contra hne; exact h a ha n hne hn
  · rintro rfl; exact smul_one a

/-- **Isaacs Lemma 6.1**: a Frobenius action gives `|N| ≡ 1 (mod |A|)`.

Proof via Burnside's lemma:
`∑_{a ∈ A} |fixedBy N a| = (#orbits) * |A|`. For `a = 1` the fixed-set is all of `N` (size `|N|`),
and for `a ≠ 1` it is `{1}` (size 1). So `|N| + (|A| - 1) = (#orbits) * |A|`, hence
`|A| ∣ |N| - 1`. -/
theorem card_modEq_one [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Fintype.card N ≡ 1 [MOD Fintype.card A] := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient A N) := Quotient.fintype _
  -- Burnside.
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A N
  -- Compute LHS: split `a = 1` from `a ≠ 1`.
  have h_one : Fintype.card (MulAction.fixedBy N (1 : A)) = Fintype.card N := by
    have h_eq : MulAction.fixedBy N (1 : A) = Set.univ := by
      ext n; simp
    calc Fintype.card (MulAction.fixedBy N (1 : A))
        = Fintype.card ((Set.univ : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = Fintype.card N := Fintype.card_congr (Equiv.Set.univ N)
  have h_other : ∀ a ∈ Finset.univ.erase (1 : A),
      Fintype.card (MulAction.fixedBy N a) = 1 := by
    intro a ha
    have ha_ne : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have h_eq := fixedBy_eq_singleton_one h ha_ne
    calc Fintype.card (MulAction.fixedBy N a)
        = Fintype.card (({1} : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = 1 := by simp
  have hLHS : ∑ a : A, Fintype.card (MulAction.fixedBy N a)
            = Fintype.card N + (Fintype.card A - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : A)), h_one,
        Finset.sum_congr rfl h_other, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, add_comm]
  rw [hLHS] at hburn
  -- Now: |N| + (|A| - 1) = (#orbits) * |A|, so |A| ∣ |N| - 1.
  haveI : Nonempty (MulAction.orbitRel.Quotient A N) := ⟨⟦1⟧⟩
  set k := Fintype.card (MulAction.orbitRel.Quotient A N)
  set a := Fintype.card A
  set n := Fintype.card N
  have ha_pos : 0 < a := Fintype.card_pos
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_pos : 0 < k := Fintype.card_pos
  -- |N| - 1 = a * (k - 1).
  have hdvd : a ∣ n - 1 := by
    refine ⟨k - 1, ?_⟩
    rw [mul_comm a (k - 1), tsub_mul, one_mul]
    omega
  exact ((Nat.modEq_iff_dvd' hn_pos).mpr hdvd).symm

/-- Corollary of Lemma 6.1: a Frobenius action implies `|N|` and `|A|` are coprime. -/
theorem coprime_card [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Nat.Coprime (Fintype.card N) (Fintype.card A) := by
  unfold Nat.Coprime
  rw [(card_modEq_one h).gcd_eq, Nat.gcd_one_left]

/-! ### Theorem 6.3: even-order Frobenius complements

If `|A|` is even and `N` is nontrivial under a Frobenius action, then `A` contains a *unique*
involution and `N` is abelian.

The proof leverages mathlib's `MonoidHom.FixedPointFree` machinery (`Mathlib/GroupTheory/
FixedPointFree.lean`): for each `t ∈ A`, the map `n ↦ t • n` is an automorphism of `N`, and the
Frobenius condition (with `t ≠ 1`) is exactly fixed-point-freeness. When `t² = 1` (involution),
the map is involutive, so by `commute_all_of_involutive` `N` is commutative, and the unique
involution follows from the fact that any involution inverts every element. -/

/-- The action of `t ∈ A` on `N` (as `MulDistribMulAction.toMulAut`) is fixed-point-free whenever
`t ≠ 1` and the action of `A` on `N` is Frobenius. -/
theorem fixedPointFree_toMulAut (h : IsFrobeniusAction A N) {t : A} (ht : t ≠ 1) :
    MonoidHom.FixedPointFree (MulDistribMulAction.toMulAut A N t) := by
  intro n hn
  by_contra hne
  exact h t ht n hne (by simpa using hn)

/-- If `t ∈ A` satisfies `t² = 1`, then its action on `N` is involutive (as a function). -/
theorem involutive_toMulAut_of_sq_eq_one {t : A} (ht_sq : t ^ 2 = 1) :
    Function.Involutive ((MulDistribMulAction.toMulAut A N t : MulAut N) : N → N) := by
  intro n
  change t • (t • n) = n
  rw [← mul_smul, ← sq, ht_sq, one_smul]

/-- **Key lemma for Thm 6.3**: an involution `t ∈ A` (`t ≠ 1`, `t² = 1`) inverts every element
of `N` under a Frobenius action. -/
theorem involution_smul_eq_inv [Finite N] (h : IsFrobeniusAction A N)
    {t : A} (ht_ne : t ≠ 1) (ht_sq : t ^ 2 = 1) (n : N) : t • n = n⁻¹ := by
  have hfree := fixedPointFree_toMulAut h ht_ne
  have hinv := involutive_toMulAut_of_sq_eq_one (A := A) (N := N) ht_sq
  have h_eq := hfree.coe_eq_inv_of_involutive hinv
  -- h_eq : ⇑(MulDistribMulAction.toMulAut A N t) = (·⁻¹)
  have := congrFun h_eq n
  simpa using this

/-- **Isaacs Theorem 6.3** (commutativity part): `|A|` even + Frobenius action on nontrivial `N`
⇒ every pair in `N` commutes. -/
theorem commute_of_card_even [Finite A] [Finite N] (h : IsFrobeniusAction A N)
    (h_even : 2 ∣ Nat.card A) (x y : N) : Commute x y := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h_even)
  have ht_ne : t ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at ht_ord; norm_num at ht_ord
  have ht_sq : t ^ 2 = 1 := by rw [← ht_ord, pow_orderOf_eq_one]
  exact (fixedPointFree_toMulAut h ht_ne).commute_all_of_involutive
    (involutive_toMulAut_of_sq_eq_one ht_sq) x y

/-- **Isaacs Theorem 6.3** (uniqueness of involution): `|A|` even + Frobenius action on nontrivial
`N` ⇒ `A` has exactly one element of order 2. -/
theorem unique_involution [Finite A] [Finite N] (h : IsFrobeniusAction A N)
    (h_even : 2 ∣ Nat.card A) (hN : Nontrivial N) :
    ∃! t : A, t ≠ 1 ∧ t ^ 2 = 1 := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h_even)
  have ht_ne : t ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at ht_ord; norm_num at ht_ord
  have ht_sq : t ^ 2 = 1 := by rw [← ht_ord, pow_orderOf_eq_one]
  refine ⟨t, ⟨ht_ne, ht_sq⟩, ?_⟩
  rintro s ⟨hs_ne, hs_sq⟩
  -- Both `s` and `t` invert every element of `N`. Hence `s * t⁻¹` fixes a nontrivial `n`.
  obtain ⟨n, hn_ne⟩ := exists_ne (1 : N)
  have hs_inv : s • n = n⁻¹ := involution_smul_eq_inv h hs_ne hs_sq n
  have ht_inv : t • n = n⁻¹ := involution_smul_eq_inv h ht_ne ht_sq n
  -- `t⁻¹ = t` since `t² = 1`.
  have ht_inv_eq : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ht_sq]
  -- `(s * t⁻¹) • n = s • (t • n) = s • n⁻¹ = (s • n)⁻¹ = n`.
  have h_st_n : (s * t⁻¹) • n = n := by
    rw [mul_smul, ht_inv_eq, ht_inv, smul_inv', hs_inv, inv_inv]
  -- By Frobenius, `s * t⁻¹ = 1`, i.e., `s = t`.
  by_contra h_neq
  have h_st_ne : s * t⁻¹ ≠ 1 := by
    intro h_eq
    exact h_neq (mul_inv_eq_one.mp h_eq)
  exact h _ h_st_ne n hn_ne h_st_n

end IsFrobeniusAction

end

section /- 6B (number-theoretic prelude): Lemma 6.16 (pp. 191-193) -/

/-! ### Isaacs Lemma 6.16

Pure number-theoretic fact used in §6B for the Sylow structure of Frobenius complements
(Cor 6.17). Independent of all preceding chapters and of §6A.

* For `p` odd: relies on the Lifting-the-Exponent lemma (mathlib
  `Int.emultiplicity_pow_sub_pow`); conclusion `i ≡ 1 (mod p^{e-1})` always holds.
* For `p = 2`: direct factorization `i^2 - 1 = (i-1)(i+1)` plus coprimality of the two
  factors with the odd residual. Three sub-cases according to which factor carries the
  bulk of the `2`-power and whether the residual is even or odd. -/

open Int

/-- Helper for the `p = 2` branch of Lemma 6.16: if `2 ^ (e + 1) ∣ i ^ 2 - 1`, then
`2 ^ e` divides one of `i - 1` or `i + 1`. -/
private theorem two_pow_dvd_or_of_sq_sub_one {e : ℕ} {i : ℤ}
    (h : (2 : ℤ) ^ (e + 1) ∣ i ^ 2 - 1) :
    (2 : ℤ) ^ e ∣ i - 1 ∨ (2 : ℤ) ^ e ∣ i + 1 := by
  -- `i` must be odd, otherwise `i^2 - 1` is odd, contradicting even divisibility.
  have h_fact : (i ^ 2 - 1 : ℤ) = (i - 1) * (i + 1) := by ring
  rw [h_fact] at h
  have h_i_odd : Odd i := by
    rcases Int.even_or_odd i with ⟨k, rfl⟩ | hodd
    · -- `i = k + k`, so `(i - 1)(i + 1) = (k+k-1)(k+k+1)` is a product of two odd numbers; odd.
      exfalso
      have h2 : (2 : ℤ) ∣ (k + k - 1) * (k + k + 1) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans h
      rcases Int.prime_two.dvd_or_dvd h2 with h2' | h2'
      · -- `2 ∣ k + k - 1` is impossible mod 2.
        omega
      · omega
    · exact hodd
  obtain ⟨j, rfl⟩ := h_i_odd
  -- Now `i = 2 j + 1`. Factorization: `(i-1)(i+1) = (2j)(2j+2) = 4 · j · (j+1)`.
  have h_dvd' : (2 : ℤ) ^ (e + 1) ∣ 4 * (j * (j + 1)) := by
    have h_re : ((2 * j + 1) - 1) * ((2 * j + 1) + 1) = 4 * (j * (j + 1)) := by ring
    rwa [h_re] at h
  -- Case split on parity of `j` (then either `j` or `j + 1` contributes a 2-power).
  rcases Int.even_or_odd j with hjeven | hjodd
  · -- `j = 2k` (well, `j = k + k`). Then `i - 1 = 4k`.
    obtain ⟨k, rfl⟩ := hjeven
    -- Coprimality: `2k + 1` (i.e. `(k + k) + 1`) is odd.
    have h_coprime : IsCoprime ((2 : ℤ) ^ (e + 1)) ((k + k) + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-k, 1, by ring⟩
    -- Rewrite `4 * ((k + k) * ((k + k) + 1))` as `(4 * (k + k)) * ((k + k) + 1)` to factor.
    have h_dvd'' : (2 : ℤ) ^ (e + 1) ∣ (4 * (k + k)) * ((k + k) + 1) := by
      convert h_dvd' using 1; ring
    have h_dvd_bulk : (2 : ℤ) ^ (e + 1) ∣ 4 * (k + k) :=
      h_coprime.dvd_of_dvd_mul_right h_dvd''
    -- `4 * (k + k) = 8 k = 2 · (4 k)`. Divide by 2: `2^e ∣ 4k = i - 1`.
    left
    rcases h_dvd_bulk with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2pow : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hm' : (4 : ℤ) * (k + k) = 2 * (2 ^ e * m) := by rw [hm, h2pow]; ring
    -- `((k + k) + 1) - 1 = k + k`, so `i - 1 = (2 j + 1) - 1` with `j = k + k`.
    linarith
  · -- `j = 2k + 1` for some `k`. Then `i + 1 = 2(2k+1) + 2 = 4(k+1)`.
    obtain ⟨k, rfl⟩ := hjodd
    right
    -- `2 k + 1` is odd.
    have h_coprime : IsCoprime ((2 : ℤ) ^ (e + 1)) (2 * k + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-k, 1, by ring⟩
    -- `4 * ((2k+1) * ((2k+1) + 1)) = (4 * (2 * (k + 1))) * (2 k + 1)`.
    have h_dvd'' : (2 : ℤ) ^ (e + 1) ∣ (4 * (2 * (k + 1))) * (2 * k + 1) := by
      convert h_dvd' using 1; ring
    have h_dvd_bulk : (2 : ℤ) ^ (e + 1) ∣ 4 * (2 * (k + 1)) :=
      h_coprime.dvd_of_dvd_mul_right h_dvd''
    rcases h_dvd_bulk with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2pow : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hm' : (4 : ℤ) * (2 * (k + 1)) = 2 * (2 ^ e * m) := by rw [hm, h2pow]; ring
    -- `(2 * (2 k + 1) + 1) + 1 = 4 k + 4 = 4 (k + 1)`, so this is `i + 1`.
    linarith

/-- **Isaacs Lemma 6.16**. Let `p` be a prime and `e` a positive integer. If `i : ℤ` satisfies
`i ^ p ≡ 1 (mod p ^ e)`, then one of the following holds:
* `i ≡ 1 (mod p ^ (e - 1))`,
* `p = 2` and `i ≡ -1 (mod 2 ^ e)`,
* `p = 2` and `i ≡ 2 ^ (e - 1) - 1 (mod 2 ^ e)`. -/
theorem pow_prime_modEq_one_cases {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) {i : ℤ}
    (h : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)]) :
    i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] ∨
    (p = 2 ∧ i ≡ -1 [ZMOD ((2 : ℤ) ^ e)]) ∨
    (p = 2 ∧ i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) := by
  -- Normalise `e = e' + 1` so `e - 1 = e'` is definitionally clean.
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.sub_add_cancel he).symm⟩
  simp only [Nat.add_sub_cancel]
  -- Convert hypothesis to divisibility (`a ≡ b [ZMOD n]` gives `n ∣ b - a`).
  have h_dvd : ((p : ℤ) ^ (e' + 1)) ∣ i ^ p - 1 := h.symm.dvd
  rcases hp.eq_two_or_odd' with rfl | hp_odd
  · -- ##### Case p = 2 #####
    rcases two_pow_dvd_or_of_sq_sub_one h_dvd with h_left | h_right
    · -- (a) holds: `2 ^ e' ∣ i - 1` ⇒ `i ≡ 1 (mod 2^e')`.
      left
      refine Int.modEq_iff_dvd.mpr ?_
      have : (1 - i : ℤ) = -(i - 1) := by ring
      rw [this]
      exact dvd_neg.mpr h_left
    · -- `2 ^ e' ∣ i + 1`. Case-split on whether `2 ^ (e' + 1) ∣ i + 1`.
      by_cases h_b : (2 : ℤ) ^ (e' + 1) ∣ i + 1
      · -- (b): `2 ^ (e' + 1) ∣ i + 1`, i.e. `i ≡ -1 (mod 2 ^ (e' + 1))`.
        right; left
        refine ⟨rfl, Int.modEq_iff_dvd.mpr ?_⟩
        have : (-1 - i : ℤ) = -(i + 1) := by ring
        rw [this]
        exact dvd_neg.mpr h_b
      · -- (c): write `i + 1 = 2 ^ e' * a` with `a` odd (else (b) would hold).
        right; right
        refine ⟨rfl, Int.modEq_iff_dvd.mpr ?_⟩
        obtain ⟨a, ha⟩ := h_right
        have ha_odd : Odd a := by
          rcases Int.even_or_odd a with hev | hodd
          · -- `a = b + b`, so `i + 1 = 2 ^ e' * (b + b) = 2 * (2^e' * b)`, contradicting `h_b`.
            exfalso
            obtain ⟨b, rfl⟩ := hev
            apply h_b
            refine ⟨b, ?_⟩
            rw [ha, pow_succ]; ring
          · exact hodd
        obtain ⟨b, rfl⟩ := ha_odd
        -- `i + 1 = 2^e' * (2 b + 1)`, so `i = 2^e' * (2 b + 1) - 1 = (2^e' - 1) + 2^(e'+1) * b`.
        -- Goal: `2 ^ (e' + 1) ∣ (2 ^ e' - 1) - i`.
        refine ⟨-b, ?_⟩
        have hi : i = (2 : ℤ) ^ e' * (2 * b + 1) - 1 := by linarith
        rw [hi, pow_succ]; ring
  · -- ##### Case p odd ##### (LTE).
    left
    -- Step 1: `p ∣ i - 1` from Fermat + hypothesis reduced modulo `p`.
    have h_p_dvd_sub : (p : ℤ) ∣ i - 1 := by
      have h_fermat : i ^ p ≡ i [ZMOD (p : ℤ)] := Int.ModEq.pow_prime_eq_self hp i
      have h_mod_p : i ^ p ≡ 1 [ZMOD (p : ℤ)] :=
        h.of_dvd (dvd_pow_self _ (Nat.succ_ne_zero _))
      exact (h_fermat.symm.trans h_mod_p).symm.dvd
    -- Step 2: `p ∤ i` (else `p ∣ 1`).
    have h_p_not_dvd_i : ¬ (p : ℤ) ∣ i := by
      intro hpi
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub hpi h_p_dvd_sub
        simpa using this
      have hp_eq : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
      have hp_eq' : p = 1 := by exact_mod_cast hp_eq
      exact hp.one_lt.ne' hp_eq'
    -- Step 3: LTE: `emultiplicity p (i^p - 1) = emultiplicity p (i - 1) + emultiplicity p p`.
    have h_LTE :=
      Int.emultiplicity_pow_sub_pow hp hp_odd (x := i) (y := 1) (by simpa using h_p_dvd_sub)
        h_p_not_dvd_i p
    rw [one_pow, hp.emultiplicity_self] at h_LTE
    -- Convert the hypothesis into an `emultiplicity` lower bound.
    have h_e_le : ((e' + 1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (i ^ p - 1) :=
      pow_dvd_iff_le_emultiplicity.mp h_dvd
    rw [h_LTE] at h_e_le
    -- `(e' + 1 : ℕ∞) ≤ m + 1 ⇒ (e' : ℕ∞) ≤ m`.
    have h_em : (e' : ℕ∞) ≤ emultiplicity (p : ℤ) (i - 1) := by
      have h_cast : ((e' + 1 : ℕ) : ℕ∞) = (e' : ℕ∞) + 1 := by push_cast; rfl
      rw [h_cast] at h_e_le
      exact (WithTop.add_le_add_iff_right WithTop.one_ne_top).mp h_e_le
    have h_pe'_dvd : (p : ℤ) ^ e' ∣ i - 1 := pow_dvd_iff_le_emultiplicity.mpr h_em
    refine Int.modEq_iff_dvd.mpr ?_
    have : (1 - i : ℤ) = -(i - 1) := by ring
    rw [this]
    exact dvd_neg.mpr h_pe'_dvd

end

section /- 6A continued: Frobenius group (subgroup pair, Thm 6.4) -/

/-! ### Definition of Frobenius group (subgroup-pair version)

A **Frobenius group** is a group `G` together with a nontrivial proper normal subgroup `N`
(the *kernel*) and a nontrivial complement `A` (the *Frobenius complement*) such that the
conjugation action of `A` on `N` is Frobenius (Isaacs's condition (1) of Thm 6.4).

Thm 6.4 in Isaacs asserts the equivalence of four conditions:
1. (conjugation-Frobenius) `∀ 1 ≠ a ∈ A, 1 ≠ n ∈ N, a n a⁻¹ ≠ n`.
2. (TI) `∀ g ∉ A, A ∩ A^g = 1`.
3. (centralizer-in-A) `∀ 1 ≠ a ∈ A, C_G(a) ⊆ A`.
4. (centralizer-in-N) `∀ 1 ≠ n ∈ N, C_G(n) ⊆ N`.

We adopt (1) as the canonical condition (it is the most directly elementary). We then prove
the cyclic equivalence of (1) ⇔ (2) ⇔ (3) directly, and supply constructors from (3) and (4).
The direction (1) ⇒ (4) requires Cor 6.6 (Frobenius's theorem on Frobenius kernels) and is
deferred. -/

/-- A **Frobenius group**: `G` has a nontrivial normal subgroup `N` (the *Frobenius kernel*)
complemented by a nontrivial subgroup `A` (the *Frobenius complement*), with the conjugation
action of `A` on `N` being Frobenius.

This is Isaacs's condition (1) of Thm 6.4; the other three equivalent conditions are proven
separately as `trivialIntersection`, `centralizer_complement_le`, and the constructors
`of_centralizer_complement_le` / `of_centralizer_kernel_le`. -/
structure IsFrobeniusGroup (G : Type*) [Group G] (N A : Subgroup G) : Prop where
  /-- The kernel `N` is normal in `G`. -/
  isNormal : N.Normal
  /-- `N` and `A` are complements: `N ⊓ A = ⊥` and the product map `N × A → G` is a bijection. -/
  isComplement : Subgroup.IsComplement' N A
  /-- The kernel is nontrivial. -/
  ne_bot_kernel : N ≠ ⊥
  /-- The complement is nontrivial. -/
  ne_bot_complement : A ≠ ⊥
  /-- The conjugation action of `A` on `N` is Frobenius (Isaacs Thm 6.4 condition (1)). -/
  conj_frobenius : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ N, n ≠ 1 → a * n * a⁻¹ ≠ n

namespace IsFrobeniusGroup

variable {G : Type*} [Group G] {N A : Subgroup G}

/-- **Isaacs Thm 6.4 (3) ⇒ (1)** (constructor). If `C_G(a) ⊆ A` for every nontrivial `a ∈ A`,
then the conjugation action of `A` on `N` is Frobenius. -/
theorem of_centralizer_complement_le
    (hN : N.Normal) (hC : Subgroup.IsComplement' N A)
    (hN_ne : N ≠ ⊥) (hA_ne : A ≠ ⊥)
    (h3 : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ A) :
    IsFrobeniusGroup G N A where
  isNormal := hN
  isComplement := hC
  ne_bot_kernel := hN_ne
  ne_bot_complement := hA_ne
  conj_frobenius := by
    intro a haA ha n hnN hn h_conj
    -- `a * n * a⁻¹ = n` ⇒ `n * a = a * n` ⇒ `n ∈ C_G(a) ⊆ A`.
    have h_an : a * n = n * a := by
      have := congrArg (· * a) h_conj
      simpa using this
    have h_comm : n * a = a * n := h_an.symm
    have hnA : n ∈ A :=
      h3 a haA ha (Subgroup.mem_centralizer_singleton_iff.mpr h_comm)
    -- `n ∈ N ∩ A = ⊥` ⇒ `n = 1`, contradicting `hn`.
    have hdisj : Disjoint N A := hC.disjoint
    exact hn (Subgroup.disjoint_def.mp hdisj hnN hnA)

/-- **Isaacs Thm 6.4 (4) ⇒ (1)** (constructor). If `C_G(n) ⊆ N` for every nontrivial `n ∈ N`,
then the conjugation action of `A` on `N` is Frobenius. -/
theorem of_centralizer_kernel_le
    (hN : N.Normal) (hC : Subgroup.IsComplement' N A)
    (hN_ne : N ≠ ⊥) (hA_ne : A ≠ ⊥)
    (h4 : ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N) :
    IsFrobeniusGroup G N A where
  isNormal := hN
  isComplement := hC
  ne_bot_kernel := hN_ne
  ne_bot_complement := hA_ne
  conj_frobenius := by
    intro a haA ha n hnN hn h_conj
    -- `a * n * a⁻¹ = n` ⇒ `a * n = n * a` ⇒ `a ∈ C_G(n) ⊆ N`.
    have h_an : a * n = n * a := by
      have := congrArg (· * a) h_conj
      simpa using this
    -- We need `a ∈ C_G(n) = { x : x * n = n * x }`.
    have h_comm : a * n = n * a := h_an
    have haN : a ∈ N :=
      h4 n hnN hn (Subgroup.mem_centralizer_singleton_iff.mpr h_comm)
    -- `a ∈ N ∩ A = ⊥` ⇒ `a = 1`, contradicting `ha`.
    have hdisj : Disjoint N A := hC.disjoint
    exact ha (Subgroup.disjoint_def.mp hdisj haN haA)

/-- Given `IsComplement' N A`, every `g : G` factors uniquely as `n * a` with `n ∈ N`, `a ∈ A`. -/
private theorem _root_.Subgroup.IsComplement'.factor
    (hC : Subgroup.IsComplement' N A) (g : G) :
    ∃ (n : G) (a : G), n ∈ N ∧ a ∈ A ∧ n * a = g := by
  obtain ⟨⟨n, a⟩, hna⟩ := (hC.existsUnique g).exists
  exact ⟨n, a, n.2, a.2, hna⟩

/-- **Isaacs Thm 6.4 (1) ⇒ (2)**: Frobenius group ⇒ trivial intersection.

If `g ∉ A`, then `A ⊓ A^g = ⊥`. (Here `A^g = g A g⁻¹ = (MulAut.conj g) '' A`.) -/
theorem trivialIntersection (h : IsFrobeniusGroup G N A) :
    ∀ g : G, g ∉ A → A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A = ⊥ := by
  intro g hg
  -- Outline: assume `A ⊓ A^g ≠ ⊥`, derive `g ∈ A`, contradiction.
  by_contra h_ne
  apply hg
  -- Factor `g = n * a` with `n ∈ N`, `a ∈ A` (from `IsComplement' N A`).
  obtain ⟨n, a, hnN, haA, hna⟩ := h.isComplement.factor g
  -- Get a nontrivial `x ∈ A ⊓ A^g`.
  have h_ne_bot : A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A ≠ ⊥ := h_ne
  obtain ⟨x, hxAg, hx_ne⟩ : ∃ x ∈ A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A, x ≠ 1 := by
    by_contra h_all
    apply h_ne_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy_ne
    exact h_all ⟨y, hy, hy_ne⟩
  rw [Subgroup.mem_inf] at hxAg
  obtain ⟨hxA, hxAg⟩ := hxAg
  -- `x = g * b * g⁻¹` for some `b ∈ A`.
  rw [Subgroup.mem_map] at hxAg
  obtain ⟨b, hbA, hxeq⟩ := hxAg
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hxeq
  -- Substitute `g = n * a`. Then `x = (n * a) * b * (n * a)⁻¹ = n * (a b a⁻¹) * n⁻¹`.
  have hxeq' : x = n * (a * b * a⁻¹) * n⁻¹ := by
    rw [← hxeq, ← hna]
    group
  -- Let `b' := a * b * a⁻¹ ∈ A`. Then `x = n * b' * n⁻¹` and `b' ∈ A`.
  set b' := a * b * a⁻¹ with hb'_def
  have hb'_mem : b' ∈ A := by
    rw [hb'_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haA hbA) (Subgroup.inv_mem _ haA)
  have hx_eq2 : x = n * b' * n⁻¹ := hxeq'
  -- Consider `b'⁻¹ * x = b'⁻¹ * (n * b' * n⁻¹)`.
  -- This is in `A` (both `b'⁻¹` and `x` are in `A`).
  -- This is also in `N`: rewrite as `(b'⁻¹ * n * b') * n⁻¹`. The factor `b'⁻¹ * n * b' ∈ N`
  -- by normality of `N`, and `n⁻¹ ∈ N`, so the product is in `N`.
  have h_comm_elem : b'⁻¹ * (n * b' * n⁻¹) ∈ A := by
    apply Subgroup.mul_mem
    · exact Subgroup.inv_mem _ hb'_mem
    · rw [← hx_eq2]; exact hxA
  have h_comm_elem' : b'⁻¹ * (n * b' * n⁻¹) ∈ N := by
    -- Rewrite as `(b'⁻¹ * n * b') * n⁻¹`.
    have h_eq : b'⁻¹ * (n * b' * n⁻¹) = (b'⁻¹ * n * b') * n⁻¹ := by group
    rw [h_eq]
    apply Subgroup.mul_mem _ _ (Subgroup.inv_mem _ hnN)
    -- `b'⁻¹ * n * b' ∈ N` by normality.
    have := h.isNormal.conj_mem' n hnN b'
    exact this
  have hdisj : Disjoint N A := h.isComplement.disjoint
  -- So `b'⁻¹ * (n * b' * n⁻¹) = 1`, i.e., `n * b' * n⁻¹ = b'`, i.e., `b'` commutes with `n`.
  have h_one : b'⁻¹ * (n * b' * n⁻¹) = 1 := Subgroup.disjoint_def.mp hdisj h_comm_elem' h_comm_elem
  have h_conj_b' : n * b' * n⁻¹ = b' := by
    have := h_one
    -- `b'⁻¹ * Y = 1` ⇒ `Y = b'`.
    have h_mul := congrArg (b' * ·) this
    simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h_mul
    exact h_mul
  -- By Frobenius condition, if `b' ≠ 1` and `n ≠ 1`, then... wait, we have `b' * n * b'⁻¹ ≠ n`.
  -- Reformulate `h_conj_b'`: `n * b' * n⁻¹ = b'` ⇔ `n * b' = b' * n` ⇔ `b' * n * b'⁻¹ = n`.
  -- So if `b' ≠ 1` and `n ≠ 1`, Frobenius gives contradiction. Hence `b' = 1` or `n = 1`.
  have h_conj_n : b' * n * b'⁻¹ = n := by
    -- `n * b' * n⁻¹ = b'` ⇒ `n * b' = b' * n`.
    have h_nb' : n * b' = b' * n := by
      have := congrArg (· * n) h_conj_b'
      simpa using this
    -- `b' * n * b'⁻¹ = (b' * n) * b'⁻¹ = (n * b') * b'⁻¹ = n`.
    rw [← h_nb', mul_inv_cancel_right]
  -- Case analysis: either `b' = 1` or `n = 1`.
  by_cases h_n_one : n = 1
  · -- `n = 1` ⇒ `g = n * a = a ∈ A`.
    rw [← hna, h_n_one, one_mul]
    exact haA
  · -- `n ≠ 1`. By Frobenius, `b' = 1`. Then `x = n * 1 * n⁻¹ = 1`, contradiction.
    by_cases h_b'_one : b' = 1
    · exfalso
      have : x = 1 := by rw [hx_eq2, h_b'_one, mul_one, mul_inv_cancel]
      exact hx_ne this
    · exfalso
      exact h.conj_frobenius b' hb'_mem h_b'_one n hnN h_n_one h_conj_n

/-- **Isaacs Thm 6.4 (2) ⇒ (3)**: Frobenius group ⇒ centralizer of any nontrivial element of `A`
is contained in `A`. -/
theorem centralizer_complement_le (h : IsFrobeniusGroup G N A) :
    ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ A := by
  intro a haA ha x hx
  -- `x * a = a * x`, so `x * a * x⁻¹ = a`, so `a = (MulAut.conj x) a⁻¹⁻¹ ∈ A.map (MulAut.conj x)`.
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  -- Want: `x ∈ A`. Assume for contradiction `x ∉ A`.
  by_contra hxA
  -- By (2), `A ⊓ A^x = ⊥`.
  have h_ti := h.trivialIntersection x hxA
  -- `a ∈ A ⊓ A^x`: indeed `a ∈ A`, and `a = (MulAut.conj x) a` (from commutativity).
  have h_a_in_conj : a ∈ Subgroup.map (MulAut.conj x).toMonoidHom A := by
    rw [Subgroup.mem_map]
    refine ⟨a, haA, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    -- `x * a * x⁻¹ = a` follows from `x * a = a * x`.
    have := hx
    calc x * a * x⁻¹ = (x * a) * x⁻¹ := by rfl
      _ = (a * x) * x⁻¹ := by rw [hx]
      _ = a := by rw [mul_inv_cancel_right]
  have h_a_in : a ∈ A ⊓ Subgroup.map (MulAut.conj x).toMonoidHom A :=
    Subgroup.mem_inf.mpr ⟨haA, h_a_in_conj⟩
  rw [h_ti, Subgroup.mem_bot] at h_a_in
  exact ha h_a_in

end IsFrobeniusGroup

end

end OddOrder.Isaacs.Ch06
