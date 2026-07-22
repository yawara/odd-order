/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Combinatorics.Colex
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Binary uniqueness modulo `2 ^ n - 1`

G. Higman, *Suzuki 2-groups*, pp. 91--92.  The final case split of Lemma 12
(types `B`, `C`, `D`) turns on a purely arithmetic fact: a sum of *distinct*
powers of two is determined modulo `2 ^ n - 1` by its set of exponents (taken
`mod n`).  Higman phrases this, in the type-`D` case, as

> "The right-hand side is the sum of the powers `2^0, 2^r, 2^s, 2^{r+s}` whose
> exponents are distinct mod `n`, hence the exponents on the left must be equal
> to them, in some order."

This file isolates that number theory, independent of the group-theoretic
setting.  Over `ZMod (2 ^ n - 1)`:

* `two_pow_zmod_card_eq_one` / `two_pow_zmod_eq_pow_mod` reduce a power `2 ^ e`
  to `2 ^ (e % n)` — the mechanism behind "exponents mod `n`", since
  `2 ^ n ≡ 1`.
* `sum_two_pow_zmod_inj_of_ssubset_range` is the uniqueness statement: the map
  `S ↦ ∑ i ∈ S, 2 ^ i` on subsets `S ⊆ range n` is injective away from the
  single wrap-around collision `∅ ↦ 0`, `range n ↦ 2 ^ n - 1 ≡ 0`.

The workhorse mathlib input is `geomSum_injective`, the injectivity of
`S ↦ ∑ i ∈ S, 2 ^ i` on all of `Finset ℕ`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open Finset

/-- `(∑ i ∈ range n, 2 ^ i) + 1 = 2 ^ n`: the carry-free form of the geometric
sum `∑ i < n, 2 ^ i = 2 ^ n - 1`. -/
theorem sum_range_two_pow_add_one (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

/-- `(2 : ZMod (2 ^ n - 1)) ^ n = 1`: the defining relation of the multiplicative
order of `2` modulo `2 ^ n - 1`. -/
theorem two_pow_zmod_card_eq_one (n : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ n = 1 := by
  have hmod : (1 : ℕ) ≡ 2 ^ n [MOD 2 ^ n - 1] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr dvd_rfl
  have hcast : ((2 ^ n : ℕ) : ZMod (2 ^ n - 1)) = ((1 : ℕ) : ZMod (2 ^ n - 1)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod.symm
  rwa [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hcast

/-- Reduce a power `2 ^ e` modulo `2 ^ n - 1` to `2 ^ (e % n)`: the source of
Higman's "exponents mod `n`". -/
theorem two_pow_zmod_eq_pow_mod (n e : ℕ) :
    (2 : ZMod (2 ^ n - 1)) ^ e = (2 : ZMod (2 ^ n - 1)) ^ (e % n) := by
  conv_lhs =>
    rw [← Nat.div_add_mod e n, pow_add, pow_mul, two_pow_zmod_card_eq_one,
      one_pow, one_mul]

/-- A distinct-power sum over a *proper* subset of `range n` is strictly below
`2 ^ n - 1`. -/
theorem sum_two_pow_lt_of_ssubset_range {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hSne : S ≠ Finset.range n) :
    (∑ i ∈ S, 2 ^ i) < 2 ^ n - 1 := by
  have hlt : (∑ i ∈ S, 2 ^ i) < ∑ i ∈ Finset.range n, 2 ^ i := by
    obtain ⟨j, hjr, hjS⟩ := Finset.exists_of_ssubset (hS.ssubset_of_ne hSne)
    exact Finset.sum_lt_sum_of_subset hS hjr hjS (Nat.two_pow_pos _)
      (fun _ _ _ => Nat.zero_le _)
  have := sum_range_two_pow_add_one n
  omega

/-- **Binary uniqueness mod `2 ^ n - 1`** (Higman, *Suzuki 2-groups*, p. 91).
Two distinct-power sums over *proper* subsets of `range n` that agree in
`ZMod (2 ^ n - 1)` have the same set of exponents.  This is the formal content
of "the exponents ... must be equal to them, in some order": the only collision
of `S ↦ ∑ i ∈ S, 2 ^ i` modulo `2 ^ n - 1` is the wrap-around
`∅ ↦ 0`, `range n ↦ 2 ^ n - 1 ≡ 0`, excluded here by properness. -/
theorem sum_two_pow_zmod_inj_of_ssubset_range {n : ℕ}
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hSne : S ≠ Finset.range n) (hTne : T ≠ Finset.range n)
    (h : ((∑ i ∈ S, 2 ^ i : ℕ) : ZMod (2 ^ n - 1)) =
      ((∑ i ∈ T, 2 ^ i : ℕ) : ZMod (2 ^ n - 1))) :
    S = T := by
  have hSlt := sum_two_pow_lt_of_ssubset_range hS hSne
  have hTlt := sum_two_pow_lt_of_ssubset_range hT hTne
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hSlt, Nat.mod_eq_of_lt hTlt] at h
  exact geomSum_injective (le_refl 2) h

/-- `ZMod`-native form of `sum_two_pow_zmod_inj_of_ssubset_range`: the powers of
`2` already live in `ZMod (2 ^ n - 1)` (as produced by taking discrete logarithms
of a primitive-root character value), rather than as a cast of a natural-number
sum. -/
theorem sum_two_pow_zmod_native_inj_of_ssubset_range {n : ℕ}
    {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (hSne : S ≠ Finset.range n) (hTne : T ≠ Finset.range n)
    (h : (∑ i ∈ S, (2 : ZMod (2 ^ n - 1)) ^ i) =
      ∑ j ∈ T, (2 : ZMod (2 ^ n - 1)) ^ j) :
    S = T := by
  refine sum_two_pow_zmod_inj_of_ssubset_range hS hT hSne hTne ?_
  rw [Nat.cast_sum, Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact h

/-- A natural number vanishes in `ZMod n` iff it vanishes mod `n` (no `NeZero`
assumption, unlike `ZMod.natCast_zmod_eq_zero_iff_dvd`). -/
theorem natCast_zmod_eq_zero_iff_mod_eq_zero {n a : ℕ} :
    (a : ZMod n) = 0 ↔ a % n = 0 := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff', Nat.zero_mod]

/-- **Complete collision description for subset power-sums mod `2 ^ n - 1`.**
Two subsets `S, T ⊆ range n` have equal power-sums `∑ i, 2 ^ i` in
`ZMod (2 ^ n - 1)` only if `S = T` or `{S, T} = {∅, range n}` — the single
wrap-around collision `0 ≡ 2 ^ n - 1`.  This upgrades
`sum_two_pow_zmod_inj_of_ssubset_range` by describing the improper cases
instead of assuming them away. -/
theorem sum_two_pow_zmod_eq_or_of_subset_range {n : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (h : (∑ i ∈ S, (2 : ZMod (2 ^ n - 1)) ^ i) =
      ∑ i ∈ T, (2 : ZMod (2 ^ n - 1)) ^ i) :
    S = T ∨ (S = Finset.range n ∧ T = ∅) ∨ (S = ∅ ∧ T = Finset.range n) := by
  have hcast : ∀ U : Finset ℕ, (∑ i ∈ U, (2 : ZMod (2 ^ n - 1)) ^ i)
      = ((∑ i ∈ U, 2 ^ i : ℕ) : ZMod (2 ^ n - 1)) := by
    intro U; push_cast; rfl
  rw [hcast, hcast, ZMod.natCast_eq_natCast_iff'] at h
  have hrange : (∑ i ∈ Finset.range n, 2 ^ i) = 2 ^ n - 1 := by
    have := sum_range_two_pow_add_one n; omega
  have hsum_pos : ∀ U : Finset ℕ, U ≠ ∅ → 0 < ∑ i ∈ U, 2 ^ i := by
    intro U hU
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    exact lt_of_lt_of_le (Nat.two_pow_pos a)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha)
  by_cases hSf : S = Finset.range n <;> by_cases hTf : T = Finset.range n
  · exact Or.inl (hSf.trans hTf.symm)
  · have hTlt := sum_two_pow_lt_of_ssubset_range hT hTf
    rw [hSf, hrange, Nat.mod_self, Nat.mod_eq_of_lt hTlt] at h
    refine Or.inr (Or.inl ⟨hSf, ?_⟩)
    by_contra hne
    have := hsum_pos T hne
    omega
  · have hSlt := sum_two_pow_lt_of_ssubset_range hS hSf
    rw [hTf, hrange, Nat.mod_self, Nat.mod_eq_of_lt hSlt] at h
    refine Or.inr (Or.inr ⟨?_, hTf⟩)
    by_contra hne
    have := hsum_pos S hne
    omega
  · have hSlt := sum_two_pow_lt_of_ssubset_range hS hSf
    have hTlt := sum_two_pow_lt_of_ssubset_range hT hTf
    rw [Nat.mod_eq_of_lt hSlt, Nat.mod_eq_of_lt hTlt] at h
    exact Or.inl (geomSum_injective (le_refl 2) h)

/-- **Collapse of a power-sum over a multiset of exponents** (carry propagation
mod `2 ^ n - 1`).  Any multiset `M` of exponents below `n` admits a Finset
`S ⊆ range n` with the same power-sum in `ZMod (2 ^ n - 1)` and `|S| ≤ |M|`;
when `M` has a repeated exponent the inequality is strict, because a repeated
power merges by the carry `2 ^ a + 2 ^ a = 2 ^ (a + 1)` (with `2 ^ n ≡ 1`
wrapping the exponent around).  This turns Higman's comparisons of "sums of
`k` powers of two" (*Suzuki 2-groups*, p. 91) into comparisons of exponent
sets, killing the repeated-exponent cases by cardinality alone. -/
theorem exists_finset_sum_two_pow_eq_of_multiset {n : ℕ} (M : Multiset ℕ)
    (hM : ∀ e ∈ M, e < n) :
    ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ Multiset.card M ∧
      (M ≠ 0 → S.Nonempty) ∧ (¬M.Nodup → S.card < Multiset.card M) ∧
      (∑ i ∈ S, (2 : ZMod (2 ^ n - 1)) ^ i) =
        (M.map fun e => (2 : ZMod (2 ^ n - 1)) ^ e).sum := by
  suffices H : ∀ (k : ℕ) (M : Multiset ℕ), Multiset.card M = k → (∀ e ∈ M, e < n) →
      ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ S.card ≤ Multiset.card M ∧
        (M ≠ 0 → S.Nonempty) ∧ (¬M.Nodup → S.card < Multiset.card M) ∧
        (∑ i ∈ S, (2 : ZMod (2 ^ n - 1)) ^ i) =
          (M.map fun e => (2 : ZMod (2 ^ n - 1)) ^ e).sum from H _ M rfl hM
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro M hcard hM
    by_cases hnd : M.Nodup
    · refine ⟨M.toFinset,
        fun x hx => Finset.mem_range.mpr (hM x (Multiset.mem_toFinset.mp hx)),
        le_of_eq (Multiset.toFinset_card_of_nodup hnd), fun h0 => ?_,
        fun h => absurd hnd h, ?_⟩
      · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h0
        exact ⟨a, Multiset.mem_toFinset.mpr ha⟩
      · rw [Finset.sum_multiset_map_count]
        exact Finset.sum_congr rfl fun x hx => by
          rw [Multiset.count_eq_one_of_mem hnd (Multiset.mem_toFinset.mp hx), one_smul]
    · -- extract a repeated exponent and merge it by the carry
      have hdup : ∃ a, 2 ≤ Multiset.count a M := by
        by_contra hno
        push Not at hno
        exact hnd (Multiset.nodup_iff_count_le_one.mpr fun a => by
          have := hno a; omega)
      obtain ⟨a, ha⟩ := hdup
      have haM : a ∈ M := Multiset.count_pos.mp (by omega)
      have han : a < n := hM a haM
      have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le a) han
      have hrep : Multiset.replicate 2 a ≤ M :=
        Multiset.le_count_iff_replicate_le.mp ha
      set M' : Multiset ℕ := M - Multiset.replicate 2 a with hM'def
      have hMeq : M = Multiset.replicate 2 a + M' := by
        rw [hM'def, add_comm]
        exact (Multiset.sub_add_cancel hrep).symm
      have hcard' : Multiset.card M = 2 + Multiset.card M' := by
        conv_lhs => rw [hMeq]
        rw [Multiset.card_add, Multiset.card_replicate]
      set M'' : Multiset ℕ := ((a + 1) % n) ::ₘ M' with hM''def
      have hcard'' : Multiset.card M'' = k - 1 := by
        rw [hM''def, Multiset.card_cons]
        omega
      have hM''mem : ∀ e ∈ M'', e < n := by
        intro e he
        rw [hM''def, Multiset.mem_cons] at he
        rcases he with rfl | he
        · exact Nat.mod_lt _ hn0
        · exact hM e (Multiset.mem_of_le tsub_le_self he)
      have hk2 : 2 ≤ k := by omega
      obtain ⟨S, hS1, hS2, hS3, _, hS5⟩ := IH (k - 1) (by omega) M'' hcard'' hM''mem
      refine ⟨S, hS1, by omega, fun _ => hS3 (Multiset.cons_ne_zero), fun _ => by omega, ?_⟩
      rw [hS5, hM''def, Multiset.map_cons, Multiset.sum_cons]
      conv_rhs => rw [hMeq]
      rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate]
      congr 1
      rw [← two_pow_zmod_eq_pow_mod, pow_succ, two_nsmul, mul_two]

/-- **The partition analysis of Higman's type-`D` case** (*Suzuki 2-groups*,
p. 92), as pure `ZMod n` arithmetic.  The four left exponents
`I, I + σ, J, J + ρ` are pairwise distinct and each lies in
`{0, ρ, σ, ρ + σ}`; matching the difference structure leaves exactly the two
solutions

* `i = r + s`, `i + s = 0`, `j = r`, `j + r = s` — giving
  `5r = 0`, `s = 2r`, `i = 3r`, `j = r`; and
* its mirror under `r ↔ s`, `i ↔ j` (interchanging the factors `X, Y`). -/
theorem higman_typeD_partition {n : ℕ} {ρ σ I J : ZMod n}
    (hρ : ρ ≠ 0) (hσ : σ ≠ 0) (hρσ : ρ + σ ≠ 0) (hρσ' : ρ ≠ σ)
    (hI : 0 = I ∨ ρ = I ∨ σ = I ∨ ρ + σ = I)
    (hIs : I + σ = 0 ∨ I + σ = ρ ∨ I + σ = σ ∨ I + σ = ρ + σ)
    (hJ : 0 = J ∨ ρ = J ∨ σ = J ∨ ρ + σ = J)
    (hJr : J + ρ = 0 ∨ J + ρ = ρ ∨ J + ρ = σ ∨ J + ρ = ρ + σ)
    (h13 : I ≠ J) (h14 : I ≠ J + ρ) (h23 : I + σ ≠ J) (h24 : I + σ ≠ J + ρ) :
    (σ = 2 * ρ ∧ 5 * ρ = 0 ∧ I = 3 * ρ ∧ J = ρ) ∨
    (ρ = 2 * σ ∧ 5 * σ = 0 ∧ I = σ ∧ J = 3 * σ) := by
  rcases hI with rfl | rfl | rfl | rfl
  · -- I = 0
    rcases hJ with rfl | rfl | rfl | rfl
    · exact absurd rfl h13
    · rcases hJr with h' | h' | h' | h'
      · exact absurd h'.symm h14
      · exact absurd (by linear_combination h') hρ
      · exact absurd (by linear_combination -h') h24
      · exact absurd (by linear_combination h') hρσ'
    · exact absurd (zero_add σ) h23
    · rcases hJr with h' | h' | h' | h'
      · exact absurd h'.symm h14
      · exact absurd (by linear_combination h') hρσ
      · exact absurd (by linear_combination -h') h24
      · exact absurd (by linear_combination h') hρ
  · -- I = ρ
    rcases hJ with rfl | rfl | rfl | rfl
    · rcases hJr with h' | h' | h' | h'
      · exact absurd (by linear_combination h') hρ
      · exact absurd (zero_add ρ).symm h14
      · exact absurd (by linear_combination h') hρσ'
      · exact absurd (by linear_combination -h') hσ
    · exact absurd rfl h13
    · rcases hJr with h' | h' | h' | h'
      · exact absurd (by linear_combination h') hρσ
      · exact absurd (by linear_combination h') hσ
      · exact absurd (by linear_combination h') hρ
      · exact absurd (add_comm ρ σ) h24
    · exact absurd rfl h23
  · -- I = σ
    rcases hIs with h'' | h'' | h'' | h''
    · -- σ + σ = 0
      rcases hJ with rfl | rfl | rfl | rfl
      · exact absurd h'' h23
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h'' - h') h24
        · exact absurd (by linear_combination h') hρ
        · exact absurd (by linear_combination -h') h14
        · exact absurd (by linear_combination h') hρσ'
      · exact absurd rfl h13
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h'' - h') h24
        · exact absurd (by linear_combination h') hρσ
        · exact absurd (by linear_combination -h') h14
        · exact absurd (by linear_combination h') hρ
    · -- σ + σ = ρ  (mirror-survivor territory)
      rcases hJ with rfl | rfl | rfl | rfl
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h') hρ
        · exact absurd (by linear_combination h'') h24
        · exact absurd (by linear_combination h') hρσ'
        · exact absurd (by linear_combination -h') hσ
      · exact absurd h'' h23
      · exact absurd rfl h13
      · rcases hJr with h' | h' | h' | h'
        · -- survivor: ρ = 2σ, 5σ = 0, I = σ, J = ρ + σ = 3σ
          exact Or.inr ⟨by linear_combination -h'', by linear_combination 2 * h'' + h',
            rfl, by linear_combination -h''⟩
        · exact absurd (by linear_combination h') hρσ
        · exact absurd h'.symm h14
        · exact absurd (by linear_combination h') hρ
    · exact absurd (by linear_combination h'') hσ
    · exact absurd (by linear_combination -h'') hρσ'
  · -- I = ρ + σ
    rcases hIs with h'' | h'' | h'' | h''
    · -- ρ + σ + σ = 0  (survivor territory)
      rcases hJ with rfl | rfl | rfl | rfl
      · exact absurd h'' h23
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h'' - h') h24
        · exact absurd (by linear_combination h') hρ
        · -- survivor: σ = 2ρ, 5ρ = 0, I = ρ + σ = 3ρ, J = ρ
          exact Or.inl ⟨by linear_combination -h', by linear_combination h'' + 2 * h',
            by linear_combination -h', rfl⟩
        · exact absurd (by linear_combination h') hρσ'
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h') hρσ
        · exact absurd (by linear_combination h') hσ
        · exact absurd (by linear_combination h') hρ
        · exact absurd (add_comm ρ σ) h14
      · exact absurd rfl h13
    · -- ρ + σ + σ = ρ
      rcases hJ with rfl | rfl | rfl | rfl
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h') hρ
        · exact absurd (by linear_combination h'') h24
        · exact absurd (by linear_combination h') hρσ'
        · exact absurd (by linear_combination -h') hσ
      · exact absurd h'' h23
      · rcases hJr with h' | h' | h' | h'
        · exact absurd (by linear_combination h') hρσ
        · exact absurd (by linear_combination h') hσ
        · exact absurd (by linear_combination h') hρ
        · exact absurd (add_comm ρ σ) h14
      · exact absurd rfl h13
    · exact absurd (by linear_combination h'') hρσ
    · exact absurd (by linear_combination h'') hσ

/-- **Higman's type-`D` congruence uniqueness** (*Suzuki 2-groups*, pp. 91–92).
If `r`, `s`, `r + s`, `r - s` are nonzero mod `n` and
`2 ^ i (1 + 2 ^ s) + 2 ^ j (1 + 2 ^ r) ≡ (1 + 2 ^ r)(1 + 2 ^ s)
(mod 2 ^ n - 1)`, then — the right-hand side being the sum of the four powers
`2 ^ 0, 2 ^ r, 2 ^ s, 2 ^ (r + s)` "whose exponents are distinct mod `n`,
hence the exponents on the left must be equal to them, in some order" — the
only solutions are `s ≡ 2r`, `5r ≡ 0`, `i ≡ 3r`, `j ≡ r (mod n)` and its
mirror image under `r ↔ s`, `i ↔ j` (interchanging the factors `X, Y`). -/
theorem higman_typeD_exponent_uniqueness {n r s i j : ℕ} (hn : 0 < n)
    (hr : (r : ZMod n) ≠ 0) (hs : (s : ZMod n) ≠ 0)
    (hrs : (r : ZMod n) + (s : ZMod n) ≠ 0) (hrs' : (r : ZMod n) ≠ (s : ZMod n))
    (h : (2 : ZMod (2 ^ n - 1)) ^ i * (1 + 2 ^ s) + 2 ^ j * (1 + 2 ^ r)
      = (1 + 2 ^ r) * (1 + 2 ^ s)) :
    ((s : ZMod n) = 2 * (r : ZMod n) ∧ 5 * (r : ZMod n) = 0 ∧
      (i : ZMod n) = 3 * (r : ZMod n) ∧ (j : ZMod n) = (r : ZMod n)) ∨
    ((r : ZMod n) = 2 * (s : ZMod n) ∧ 5 * (s : ZMod n) = 0 ∧
      (i : ZMod n) = (s : ZMod n) ∧ (j : ZMod n) = 3 * (s : ZMod n)) := by
  have bridge : ∀ a b : ℕ, a % n = b % n → (a : ZMod n) = (b : ZMod n) :=
    fun a b hab => (ZMod.natCast_eq_natCast_iff' a b n).mpr hab
  have bridge' : ∀ a b : ℕ, (a : ZMod n) = (b : ZMod n) → a % n = b % n :=
    fun a b hab => (ZMod.natCast_eq_natCast_iff' a b n).mp hab
  -- the four right-hand exponents are pairwise distinct mod `n`
  have t01 : (0 : ℕ) ≠ r % n := fun hh => hr (by
    have := bridge 0 r (by rw [Nat.zero_mod]; exact hh)
    simpa using this.symm)
  have t02 : (0 : ℕ) ≠ s % n := fun hh => hs (by
    have := bridge 0 s (by rw [Nat.zero_mod]; exact hh)
    simpa using this.symm)
  have t03 : (0 : ℕ) ≠ (r + s) % n := fun hh => hrs (by
    have := bridge 0 (r + s) (by rw [Nat.zero_mod]; exact hh)
    push_cast at this
    linear_combination -this)
  have t12 : r % n ≠ s % n := fun hh => hrs' (bridge r s hh)
  have t13 : r % n ≠ (r + s) % n := fun hh => hs (by
    have := bridge r (r + s) hh
    push_cast at this
    linear_combination -this)
  have t23 : s % n ≠ (r + s) % n := fun hh => hr (by
    have := bridge s (r + s) hh
    push_cast at this
    linear_combination -this)
  -- the right-hand exponent set and its power-sum
  have hTnotmem0 : (0 : ℕ) ∉ (insert (r % n) (insert (s % n) {(r + s) % n}) : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hh | hh | hh)
    exacts [t01 hh, t02 hh, t03 hh]
  have hTnotmem1 : r % n ∉ (insert (s % n) {(r + s) % n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hh | hh)
    exacts [t12 hh, t13 hh]
  have hTnotmem2 : s % n ∉ ({(r + s) % n} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact t23
  have hTsub : (insert 0 (insert (r % n) (insert (s % n) {(r + s) % n})) : Finset ℕ)
      ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_range.mpr hn
    all_goals exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  have hTsum : (∑ x ∈ insert 0 (insert (r % n) (insert (s % n) {(r + s) % n})),
      (2 : ZMod (2 ^ n - 1)) ^ x) = (1 + 2 ^ r) * (1 + 2 ^ s) := by
    rw [Finset.sum_insert hTnotmem0, Finset.sum_insert hTnotmem1,
      Finset.sum_insert hTnotmem2, Finset.sum_singleton]
    simp only [← two_pow_zmod_eq_pow_mod]
    ring1
  -- the left-hand exponents, as a multiset (repetitions possible a priori)
  set L : Multiset ℕ := {i % n, (i + s) % n, j % n, (j + r) % n} with hLdef
  have hLmem : ∀ e ∈ L, e < n := by
    intro e he
    rw [hLdef] at he
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ hn
  have hLsum : (L.map fun e => (2 : ZMod (2 ^ n - 1)) ^ e).sum
      = (1 + 2 ^ r) * (1 + 2 ^ s) := by
    rw [hLdef]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    simp only [← two_pow_zmod_eq_pow_mod]
    linear_combination h
  by_cases hnd : L.Nodup
  · -- distinct left exponents: the exponent sets must be equal
    rw [hLdef] at hnd
    simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, and_true, not_or] at hnd
    obtain ⟨⟨l12, l13, l14⟩, ⟨l23, l24⟩, l34⟩ := hnd
    have hSsub : (insert (i % n) (insert ((i + s) % n) (insert (j % n) {(j + r) % n})) :
        Finset ℕ) ⊆ Finset.range n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    have hSsum : (∑ x ∈ insert (i % n) (insert ((i + s) % n) (insert (j % n) {(j + r) % n})),
        (2 : ZMod (2 ^ n - 1)) ^ x) = (1 + 2 ^ r) * (1 + 2 ^ s) := by
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (hh | hh | hh)
          exacts [l12 hh, l13 hh, l14 hh]),
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (hh | hh)
          exacts [l23 hh, l24 hh]),
        Finset.sum_insert (by simp only [Finset.mem_singleton]; exact l34),
        Finset.sum_singleton]
      simp only [← two_pow_zmod_eq_pow_mod]
      linear_combination h
    rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub (hSsum.trans hTsum.symm) with
      hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
    · -- set equality: each left exponent is one of `0, r, s, r + s` mod `n`
      have hmem : ∀ x ∈ (insert (i % n) (insert ((i + s) % n)
          (insert (j % n) {(j + r) % n})) : Finset ℕ),
          x = 0 ∨ x = r % n ∨ x = s % n ∨ x = (r + s) % n := by
        intro x hx
        rw [hST] at hx
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
      have hmemI := hmem (i % n) (by simp)
      have hmemIs := hmem ((i + s) % n) (by simp)
      have hmemJ := hmem (j % n) (by simp)
      have hmemJr := hmem ((j + r) % n) (by simp)
      -- convert the plain memberships (for `i`, `j`) to `ZMod n`
      have conv : ∀ a : ℕ, a % n = 0 ∨ a % n = r % n ∨ a % n = s % n ∨ a % n = (r + s) % n →
          0 = (a : ZMod n) ∨ (r : ZMod n) = a ∨ (s : ZMod n) = a ∨
            (r : ZMod n) + s = a := by
        intro a ha
        rcases ha with hh | hh | hh | hh
        · refine Or.inl ?_
          have := bridge a 0 (by rw [Nat.zero_mod]; exact hh)
          simpa using this.symm
        · exact Or.inr (Or.inl (bridge r a hh.symm))
        · exact Or.inr (Or.inr (Or.inl (bridge s a hh.symm)))
        · refine Or.inr (Or.inr (Or.inr ?_))
          have := bridge (r + s) a hh.symm
          push_cast at this
          exact this
      -- convert the shifted memberships (for `i + s`, `j + r`) to `ZMod n`
      have convIs : (i : ZMod n) + (s : ZMod n) = 0 ∨ (i : ZMod n) + (s : ZMod n) = r ∨
          (i : ZMod n) + (s : ZMod n) = s ∨
          (i : ZMod n) + (s : ZMod n) = (r : ZMod n) + s := by
        rcases hmemIs with hh | hh | hh | hh
        · refine Or.inl ?_
          have := bridge (i + s) 0 (by rw [Nat.zero_mod]; exact hh)
          push_cast at this
          exact this
        · refine Or.inr (Or.inl ?_)
          have := bridge (i + s) r hh
          push_cast at this
          exact this
        · refine Or.inr (Or.inr (Or.inl ?_))
          have := bridge (i + s) s hh
          push_cast at this
          exact this
        · refine Or.inr (Or.inr (Or.inr ?_))
          have := bridge (i + s) (r + s) hh
          push_cast at this
          exact this
      have convJr : (j : ZMod n) + (r : ZMod n) = 0 ∨ (j : ZMod n) + (r : ZMod n) = r ∨
          (j : ZMod n) + (r : ZMod n) = s ∨
          (j : ZMod n) + (r : ZMod n) = (r : ZMod n) + s := by
        rcases hmemJr with hh | hh | hh | hh
        · refine Or.inl ?_
          have := bridge (j + r) 0 (by rw [Nat.zero_mod]; exact hh)
          push_cast at this
          exact this
        · refine Or.inr (Or.inl ?_)
          have := bridge (j + r) r hh
          push_cast at this
          exact this
        · refine Or.inr (Or.inr (Or.inl ?_))
          have := bridge (j + r) s hh
          push_cast at this
          exact this
        · refine Or.inr (Or.inr (Or.inr ?_))
          have := bridge (j + r) (r + s) hh
          push_cast at this
          exact this
      -- distinctness in `ZMod n`
      have d13 : (i : ZMod n) ≠ (j : ZMod n) := fun hh => l13 (bridge' i j hh)
      have d14 : (i : ZMod n) ≠ (j : ZMod n) + (r : ZMod n) := fun hh =>
        l14 (bridge' i (j + r) (by push_cast; exact hh))
      have d23 : (i : ZMod n) + (s : ZMod n) ≠ (j : ZMod n) := fun hh =>
        l23 (bridge' (i + s) j (by push_cast; exact hh))
      have d24 : (i : ZMod n) + (s : ZMod n) ≠ (j : ZMod n) + (r : ZMod n) := fun hh =>
        l24 (bridge' (i + s) (j + r) (by push_cast; exact hh))
      exact higman_typeD_partition hr hs hrs hrs' (conv i hmemI) convIs (conv j hmemJ)
        convJr d13 d14 d23 d24
    · exact absurd hT0 (Finset.insert_ne_empty _ _)
    · exact absurd hS0 (Finset.insert_ne_empty _ _)
  · -- a repeated left exponent collapses by the carry: cardinality contradiction
    obtain ⟨S, hS1, _, hS3, hS4, hS5⟩ := exists_finset_sum_two_pow_eq_of_multiset L hLmem
    have hcard4 : Multiset.card L = 4 := by
      rw [hLdef]
      simp [Multiset.insert_eq_cons]
    have hSlt : S.card < 4 := hcard4 ▸ hS4 hnd
    have hSne : S.Nonempty := hS3 (by
      rw [hLdef]
      simp only [Multiset.insert_eq_cons]
      exact Multiset.cons_ne_zero)
    rcases sum_two_pow_zmod_eq_or_of_subset_range hS1 hTsub
        (hS5.trans (hLsum.trans hTsum.symm)) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
    · have hTcard : (insert 0 (insert (r % n) (insert (s % n) {(r + s) % n})) :
          Finset ℕ).card = 4 := by
        rw [Finset.card_insert_of_notMem hTnotmem0, Finset.card_insert_of_notMem hTnotmem1,
          Finset.card_insert_of_notMem hTnotmem2, Finset.card_singleton]
      rw [hST, hTcard] at hSlt
      omega
    · exact absurd hT0 (Finset.insert_ne_empty _ _)
    · rw [hS0] at hSne
      exact absurd hSne Finset.not_nonempty_empty

/-- **Higman's type-`C` congruence uniqueness** (*Suzuki 2-groups*, p. 91).
With `0 < r ≤ n/2`, the congruence
`1 + 2 ^ s (1 + 2 ^ r) ≡ 2 ^ t (1 + 2 ^ r) (mod 2 ^ n - 1)` — a sum of three
powers of two against a sum of two, so that a carry must merge exactly one
pair — has the single surviving solution `s ≡ r + 1`, `t ≡ 1 (mod n)` and
`2r + 1 = n` (in particular `n` is odd).  Here `s` plays the role of Higman's
`s - 1`; of his six candidate solutions, two are immediately contradictory,
two force `r ≡ 0`, and `s ≡ 1, t ≡ r, 2r ≡ 1 (mod n)` conflicts with
`0 < r ≤ n/2`. -/
theorem higman_typeC_exponent_uniqueness {n r s t : ℕ} (hr : 0 < r) (h2r : 2 * r ≤ n)
    (h : (1 : ZMod (2 ^ n - 1)) + 2 ^ s * (1 + 2 ^ r) = 2 ^ t * (1 + 2 ^ r)) :
    2 * r + 1 = n ∧ (s : ZMod n) = (r : ZMod n) + 1 ∧ (t : ZMod n) = 1 := by
  have hn2 : 2 ≤ n := le_trans (by omega) h2r
  have hn : 0 < n := by omega
  have hrn : r < n := by omega
  have hrm : r % n = r := Nat.mod_eq_of_lt hrn
  have h1n : (1 : ℕ) < n := by omega
  have h1m : (1 : ℕ) % n = 1 := Nat.mod_eq_of_lt h1n
  have bridge : ∀ a b : ℕ, a % n = b % n → (a : ZMod n) = (b : ZMod n) :=
    fun a b hab => (ZMod.natCast_eq_natCast_iff' a b n).mpr hab
  have onene : ((1 : ℕ) : ZMod n) ≠ 0 := by
    intro hh
    rw [natCast_zmod_eq_zero_iff_mod_eq_zero, h1m] at hh
    omega
  -- the right-hand exponent pair `{t, t + r}` is distinct mod `n`
  have tdist : t % n ≠ (t + r) % n := by
    intro hh
    have hcast := bridge t (t + r) hh
    push_cast at hcast
    have hr0 : (r : ZMod n) = 0 := by linear_combination -hcast
    rw [natCast_zmod_eq_zero_iff_mod_eq_zero, hrm] at hr0
    omega
  have hTsub : ({t % n, (t + r) % n} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  have hTsum : (∑ x ∈ ({t % n, (t + r) % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
      = 2 ^ t * (1 + 2 ^ r) := by
    rw [Finset.sum_pair tdist]
    simp only [← two_pow_zmod_eq_pow_mod]
    ring1
  have hsing_sub : ({2 % n} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  by_cases hA : s % n = 0
  · -- `s ≡ 0`: the left side collapses to `2 ^ 1 + 2 ^ r`; every match dies
    have hpows : (2 : ZMod (2 ^ n - 1)) ^ s = 1 := by
      rw [two_pow_zmod_eq_pow_mod, hA, pow_zero]
    by_cases hr1 : r = 1
    · -- further collapse to the single power `2 ^ 2`
      subst hr1
      have hSsum : (∑ x ∈ ({2 % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
          = 2 ^ t * (1 + 2 ^ 1) := by
        rw [Finset.sum_singleton, ← two_pow_zmod_eq_pow_mod, ← h, hpows]
        ring1
      rcases sum_two_pow_zmod_eq_or_of_subset_range hsing_sub hTsub
          (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
      · have := congrArg Finset.card hST
        rw [Finset.card_singleton, Finset.card_pair tdist] at this
        omega
      · exact absurd hT0 (Finset.insert_ne_empty _ _)
      · exact absurd hS0 (Finset.singleton_ne_empty _)
    · -- left set `{1, r}`: both matchings with `{t, t + r}` are contradictory
      have h1r : (1 : ℕ) ≠ r := fun hh => hr1 hh.symm
      have hSsub : ({1, r} : Finset ℕ) ⊆ Finset.range n := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_range.mpr h1n
        · exact Finset.mem_range.mpr hrn
      have hSsum : (∑ x ∈ ({1, r} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
          = 2 ^ t * (1 + 2 ^ r) := by
        rw [Finset.sum_pair h1r, ← h, hpows]
        ring1
      rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
          (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
      · have hmem1 : (1 : ℕ) ∈ ({t % n, (t + r) % n} : Finset ℕ) := by
          rw [← hST]; simp
        have hmemr : r ∈ ({t % n, (t + r) % n} : Finset ℕ) := by
          rw [← hST]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmemr
        rcases hmem1 with h1 | h1
        · rcases hmemr with h2 | h2
          · -- `r = t ≡ 1`: against `r ≠ 1`
            exact absurd (h2.trans h1.symm) hr1
          · -- `t ≡ 1` and `t + r ≡ r` force `1 ≡ 0`
            have e1 : (1 : ZMod n) = (t : ZMod n) := by
              have := bridge 1 t (by rw [h1m]; exact h1)
              simpa using this
            have e2 : (t : ZMod n) = 0 := by
              have := bridge r (t + r) (by rw [hrm]; exact h2)
              push_cast at this
              linear_combination -this
            exact absurd (by rw [Nat.cast_one]; exact e1.trans e2) onene
        · rcases hmemr with h2 | h2
          · -- `t ≡ r` and `t + r ≡ 1` force `2r ≡ 1 (mod n)`: impossible for
            -- `0 < 2r ≤ n`
            have e1 : (1 : ZMod n) = (t : ZMod n) + r := by
              have := bridge 1 (t + r) (by rw [h1m]; exact h1)
              push_cast at this
              exact this
            have e2 : (r : ZMod n) = (t : ZMod n) := bridge r t (by rw [hrm]; exact h2)
            have h2r1 : (2 * r) % n = 1 % n := (ZMod.natCast_eq_natCast_iff' _ _ n).mp (by
              push_cast
              linear_combination -e1 + e2)
            rw [h1m] at h2r1
            rcases Nat.lt_or_ge (2 * r) n with hlt | hge
            · rw [Nat.mod_eq_of_lt hlt] at h2r1
              omega
            · have he : 2 * r = n := by omega
              rw [he, Nat.mod_self] at h2r1
              omega
          · -- `r = t + r ≡ 1`: against `r ≠ 1`
            exact absurd (h2.trans h1.symm) hr1
      · exact absurd hT0 (Finset.insert_ne_empty _ _)
      · exact absurd hS0 (Finset.insert_ne_empty _ _)
  · by_cases hB : (s + r) % n = 0
    · -- `s + r ≡ 0`: the left side collapses to `2 ^ 1 + 2 ^ s`
      have hpowsr : (2 : ZMod (2 ^ n - 1)) ^ (s + r) = 1 := by
        rw [two_pow_zmod_eq_pow_mod, hB, pow_zero]
      have eB : (s : ZMod n) + (r : ZMod n) = 0 := by
        have := bridge (s + r) 0 (by rw [Nat.zero_mod]; exact hB)
        push_cast at this
        exact this
      by_cases hs1 : s % n = 1
      · -- further collapse to the single power `2 ^ 2`
        have hpows2 : (2 : ZMod (2 ^ n - 1)) ^ s = 2 := by
          rw [two_pow_zmod_eq_pow_mod, hs1, pow_one]
        have hSsum : (∑ x ∈ ({2 % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
            = 2 ^ t * (1 + 2 ^ r) := by
          rw [Finset.sum_singleton, ← two_pow_zmod_eq_pow_mod, ← h]
          linear_combination -hpows2 - hpowsr
        rcases sum_two_pow_zmod_eq_or_of_subset_range hsing_sub hTsub
            (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
        · have := congrArg Finset.card hST
          rw [Finset.card_singleton, Finset.card_pair tdist] at this
          omega
        · exact absurd hT0 (Finset.insert_ne_empty _ _)
        · exact absurd hS0 (Finset.singleton_ne_empty _)
      · -- left set `{1, s}`: the matching `t ≡ 1, s ≡ t + r` is the survivor
        have h1s : (1 : ℕ) ≠ s % n := fun hh => hs1 hh.symm
        have hSsub : ({1, s % n} : Finset ℕ) ⊆ Finset.range n := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_range.mpr h1n
          · exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
        have hSsum : (∑ x ∈ ({1, s % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
            = 2 ^ t * (1 + 2 ^ r) := by
          rw [Finset.sum_pair h1s, ← two_pow_zmod_eq_pow_mod, ← h]
          linear_combination -hpowsr
        rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
            (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
        · have hmem1 : (1 : ℕ) ∈ ({t % n, (t + r) % n} : Finset ℕ) := by
            rw [← hST]; simp
          have hmems : s % n ∈ ({t % n, (t + r) % n} : Finset ℕ) := by
            rw [← hST]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmems
          rcases hmem1 with h1 | h1
          · rcases hmems with h2 | h2
            · -- `s ≡ t ≡ 1`: against `s ≢ 1`
              exact absurd (h2.trans h1.symm) hs1
            · -- **the survivor**: `t ≡ 1`, `s ≡ t + r ≡ r + 1`, `2r + 1 = n`
              have et : (t : ZMod n) = 1 := by
                have := bridge t 1 (by rw [h1m]; exact h1.symm)
                simpa using this
              have es : (s : ZMod n) = (t : ZMod n) + r := by
                have := bridge s (t + r) h2
                push_cast at this
                exact this
              have h2r10 : ((2 * r + 1 : ℕ) : ZMod n) = 0 := by
                push_cast
                linear_combination eB - es - et
              rw [natCast_zmod_eq_zero_iff_mod_eq_zero] at h2r10
              have hfin : 2 * r + 1 = n := by
                rcases Nat.lt_or_ge (2 * r + 1) n with hlt | hge
                · rw [Nat.mod_eq_of_lt hlt] at h2r10
                  omega
                · have he : 2 * r + 1 = n ∨ 2 * r + 1 = n + 1 := by omega
                  rcases he with he | he
                  · exact he
                  · rw [he, Nat.add_mod_left, h1m] at h2r10
                    omega
              exact ⟨hfin, by linear_combination es + et, et⟩
          · rcases hmems with h2 | h2
            · -- `t ≡ s ≡ -r` and `t + r ≡ 1` force `1 ≡ 0`
              have e1 : (1 : ZMod n) = (t : ZMod n) + r := by
                have := bridge 1 (t + r) (by rw [h1m]; exact h1)
                push_cast at this
                exact this
              have e2 : (s : ZMod n) = (t : ZMod n) := bridge s t h2
              exact absurd (by
                rw [Nat.cast_one]
                linear_combination e1 - e2 + eB) onene
            · -- `s ≡ t + r ≡ 1`: against `s ≢ 1`
              exact absurd (h2.trans h1.symm) hs1
        · exact absurd hT0 (Finset.insert_ne_empty _ _)
        · exact absurd hS0 (Finset.insert_ne_empty _ _)
    · -- no collapse: three distinct powers against two — impossible
      have l01 : (0 : ℕ) ≠ s % n := fun hh => hA hh.symm
      have l02 : (0 : ℕ) ≠ (s + r) % n := fun hh => hB hh.symm
      have l12 : s % n ≠ (s + r) % n := by
        intro hh
        have hcast := bridge s (s + r) hh
        push_cast at hcast
        have hr0 : (r : ZMod n) = 0 := by linear_combination -hcast
        rw [natCast_zmod_eq_zero_iff_mod_eq_zero, hrm] at hr0
        omega
      have hSnotmem : (0 : ℕ) ∉ (insert (s % n) {(s + r) % n} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (hh | hh)
        exacts [l01 hh, l02 hh]
      have hSsub : ({0, s % n, (s + r) % n} : Finset ℕ) ⊆ Finset.range n := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact Finset.mem_range.mpr hn
        all_goals exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
      have hSsum : (∑ x ∈ ({0, s % n, (s + r) % n} : Finset ℕ),
          (2 : ZMod (2 ^ n - 1)) ^ x) = 2 ^ t * (1 + 2 ^ r) := by
        rw [Finset.sum_insert hSnotmem, Finset.sum_pair l12]
        simp only [← two_pow_zmod_eq_pow_mod]
        rw [← h]
        ring1
      rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
          (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
      · have := congrArg Finset.card hST
        rw [Finset.card_insert_of_notMem hSnotmem, Finset.card_pair l12,
          Finset.card_pair tdist] at this
        omega
      · exact absurd hT0 (Finset.insert_ne_empty _ _)
      · exact absurd hS0 (Finset.insert_ne_empty _ _)

/-- **Two powers of two summing to one power** (Higman's eigenvalue argument
for `θ = φ = 1`, *Suzuki 2-groups*, p. 90): if
`2 ^ a + 2 ^ b ≡ 2 ^ c (mod 2 ^ n - 1)` then `a ≡ b` and `c ≡ a + 1 (mod n)`
— a carry must merge the two powers.  This is why `[x_i, y_j] = 0` for
`i ≠ j` in the type-`B(n, 1, ε)` case: `λ^{2^i + 2^j}` is an eigenvalue of `ξ`
on `Φ(G)` (all of the form `λ^{2^{k+1}}`) only if `i = j`. -/
theorem higman_two_pow_add_eq_two_pow {n a b c : ℕ} (hn : 0 < n)
    (h : (2 : ZMod (2 ^ n - 1)) ^ a + 2 ^ b = 2 ^ c) :
    (a : ZMod n) = (b : ZMod n) ∧ (c : ZMod n) = (a : ZMod n) + 1 := by
  have bridge : ∀ x y : ℕ, x % n = y % n → (x : ZMod n) = (y : ZMod n) :=
    fun x y hxy => (ZMod.natCast_eq_natCast_iff' x y n).mpr hxy
  have hTsub : ({c % n} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  have hTsum : (∑ x ∈ ({c % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x) = 2 ^ c := by
    rw [Finset.sum_singleton, ← two_pow_zmod_eq_pow_mod]
  by_cases hab : a % n = b % n
  · -- the powers merge: `2 ^ (a + 1) = 2 ^ c`
    refine ⟨bridge a b hab, ?_⟩
    have hmerge : (∑ x ∈ ({(a + 1) % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
        = 2 ^ c := by
      rw [Finset.sum_singleton, ← two_pow_zmod_eq_pow_mod, ← h,
        two_pow_zmod_eq_pow_mod n b, ← hab, ← two_pow_zmod_eq_pow_mod,
        pow_succ, mul_two]
    rcases sum_two_pow_zmod_eq_or_of_subset_range (by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_range.mpr (Nat.mod_lt _ hn)) hTsub
        (hmerge.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
    · have := Finset.singleton_injective hST
      have hcast := bridge (a + 1) c this
      push_cast at hcast
      exact hcast.symm
    · exact absurd hT0 (Finset.singleton_ne_empty _)
    · exact absurd hS0 (Finset.singleton_ne_empty _)
  · -- two distinct powers cannot equal a single one
    exfalso
    have hSsub : ({a % n, b % n} : Finset ℕ) ⊆ Finset.range n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    have hSsum : (∑ x ∈ ({a % n, b % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
        = 2 ^ c := by
      rw [Finset.sum_pair hab, ← two_pow_zmod_eq_pow_mod, ← two_pow_zmod_eq_pow_mod]
      exact h
    rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
        (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
    · have := congrArg Finset.card hST
      rw [Finset.card_pair hab, Finset.card_singleton] at this
      omega
    · exact absurd hT0 (Finset.singleton_ne_empty _)
    · exact absurd hS0 (Finset.insert_ne_empty _ _)

/-- **Higman's `s = ±r` matching** (*Suzuki 2-groups*, p. 91, case
`θ = φ ≠ 1`): if `r, s` are nonzero mod `n` and
`2 ^ i (1 + 2 ^ s) ≡ 2 ^ t (1 + 2 ^ r) (mod 2 ^ n - 1)` then `s ≡ r` or
`s ≡ -r (mod n)`.  This is why `[x_i, y_j] = 0` for `|j - i| ≠ r` in the
type-`B(n, θ, ε)` case: `λ^{2^i (1 + 2^{j-i})}` matches an eigenvalue
`λ^{2^t (1 + 2^r)}` of `ξ` on `Φ(G)` only if `j - i ≡ ±r`. -/
theorem higman_typeB_exponent_pm {n r s i t : ℕ} (hn : 0 < n)
    (hr : (r : ZMod n) ≠ 0) (hs : (s : ZMod n) ≠ 0)
    (h : (2 : ZMod (2 ^ n - 1)) ^ i * (1 + 2 ^ s) = 2 ^ t * (1 + 2 ^ r)) :
    (s : ZMod n) = (r : ZMod n) ∨ (s : ZMod n) + (r : ZMod n) = 0 := by
  have bridge : ∀ x y : ℕ, x % n = y % n → (x : ZMod n) = (y : ZMod n) :=
    fun x y hxy => (ZMod.natCast_eq_natCast_iff' x y n).mpr hxy
  have hsd : i % n ≠ (i + s) % n := by
    intro hh
    have := bridge i (i + s) hh
    push_cast at this
    exact hs (by linear_combination -this)
  have hrd : t % n ≠ (t + r) % n := by
    intro hh
    have := bridge t (t + r) hh
    push_cast at this
    exact hr (by linear_combination -this)
  have hSsub : ({i % n, (i + s) % n} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  have hTsub : ({t % n, (t + r) % n} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
  have hSsum : (∑ x ∈ ({i % n, (i + s) % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
      = 2 ^ t * (1 + 2 ^ r) := by
    rw [Finset.sum_pair hsd]
    simp only [← two_pow_zmod_eq_pow_mod]
    linear_combination h
  have hTsum : (∑ x ∈ ({t % n, (t + r) % n} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
      = 2 ^ t * (1 + 2 ^ r) := by
    rw [Finset.sum_pair hrd]
    simp only [← two_pow_zmod_eq_pow_mod]
    ring1
  rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
      (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
  · have hmemi : i % n ∈ ({t % n, (t + r) % n} : Finset ℕ) := by
      rw [← hST]; simp
    have hmemis : (i + s) % n ∈ ({t % n, (t + r) % n} : Finset ℕ) := by
      rw [← hST]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemi hmemis
    rcases hmemi with h1 | h1
    · rcases hmemis with h2 | h2
      · exact absurd (h1.trans h2.symm) hsd
      · -- `i ≡ t` and `i + s ≡ t + r`: `s ≡ r`
        refine Or.inl ?_
        have e1 := bridge i t h1
        have e2 := bridge (i + s) (t + r) h2
        push_cast at e2
        linear_combination e2 - e1
    · rcases hmemis with h2 | h2
      · -- `i ≡ t + r` and `i + s ≡ t`: `s + r ≡ 0`
        refine Or.inr ?_
        have e1 := bridge i (t + r) h1
        have e2 := bridge (i + s) t h2
        push_cast at e1 e2
        linear_combination e2 - e1
      · exact absurd (h1.trans h2.symm) hsd
  · exact absurd hT0 (Finset.insert_ne_empty _ _)
  · exact absurd hS0 (Finset.insert_ne_empty _ _)

/-! ### Bridges from eigenvalue equations to the exponent congruences

Higman's case analysis starts from equations between powers of a primitive
`(2 ^ n - 1)`-st root of unity `ν` (an eigenvalue of the cyclic actor `ξ`) and
converts them into congruences between the exponents mod `2 ^ n - 1` — the
inputs of `higman_typeC_exponent_uniqueness` and
`higman_typeD_exponent_uniqueness` above.  The conversion is
`pow_eq_pow_iff_modEq` plus exponent algebra; no discrete logarithm is
needed. -/

/-- An element of multiplicative order `2 ^ n - 1` is fixed by the `n`-th
Frobenius power: `ν ^ (2 ^ n) = ν`.  This renormalises Higman's eigenvalue
equations `λ^{2^i} μ^{2^j} = ν^{2^k}` to `k = 0` by raising both sides to the
power `2 ^ (n - k)`. -/
theorem pow_two_pow_eq_self_of_orderOf {F : Type*} [Monoid F] {nu : F} {n : ℕ}
    (hord : orderOf nu = 2 ^ n - 1) : nu ^ 2 ^ n = nu := by
  have h1 : 2 ^ n = (2 ^ n - 1) + 1 := by
    have : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [h1, pow_succ, ← hord, pow_orderOf_eq_one, one_mul]

/-- **The type-`C` eigenvalue bridge** (Higman, *Suzuki 2-groups*, p. 91).
From `λ^{1 + 2^s (1 + 2^r)} = λ^{2^t (1 + 2^r)}` for `λ` of order `2 ^ n - 1`
(the matching of the eigenvalue of `[x₀, y_{s+1}] ≠ 0` with an eigenvalue on
`Φ(G)`), the exponents agree mod `2 ^ n - 1`, in the form consumed by
`higman_typeC_exponent_uniqueness`. -/
theorem higman_typeC_congruence_of_pow_eq {F : Type*} [Monoid F] {lam : F}
    {n r s t : ℕ} (hn : 0 < n) (hord : orderOf lam = 2 ^ n - 1)
    (h : lam ^ (1 + 2 ^ s * (1 + 2 ^ r)) = lam ^ (2 ^ t * (1 + 2 ^ r))) :
    (1 : ZMod (2 ^ n - 1)) + 2 ^ s * (1 + 2 ^ r) = 2 ^ t * (1 + 2 ^ r) := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder lam := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmod : 1 + 2 ^ s * (1 + 2 ^ r) ≡ 2 ^ t * (1 + 2 ^ r) [MOD 2 ^ n - 1] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp h
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  exact hcast

/-- **The type-`D` eigenvalue bridge** (Higman, *Suzuki 2-groups*, p. 91).
From `λ^{2^i} μ^{2^j} = ν` with `ν = λ^{1 + 2^r} = μ^{1 + 2^s}` of order
`2 ^ n - 1` (a nonzero product `[x_i, y_j]` on the `ν`-eigenline `v₀`), raising
to the power `(1 + 2^r)(1 + 2^s)` gives
`2^i (1 + 2^s) + 2^j (1 + 2^r) ≡ (1 + 2^r)(1 + 2^s) (mod 2 ^ n - 1)`, in the
form consumed by `higman_typeD_exponent_uniqueness`. -/
theorem higman_typeD_congruence_of_pow_eq {F : Type*} [CommMonoid F]
    {nu lam mu : F} {n r s i j : ℕ} (hn : 0 < n) (hord : orderOf nu = 2 ^ n - 1)
    (hlam : lam ^ (1 + 2 ^ r) = nu) (hmu : mu ^ (1 + 2 ^ s) = nu)
    (h : lam ^ 2 ^ i * mu ^ 2 ^ j = nu) :
    (2 : ZMod (2 ^ n - 1)) ^ i * (1 + 2 ^ s) + 2 ^ j * (1 + 2 ^ r)
      = (1 + 2 ^ r) * (1 + 2 ^ s) := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder nu := orderOf_pos_iff.mp (by rw [hord]; omega)
  have key : nu ^ (2 ^ i * (1 + 2 ^ s) + 2 ^ j * (1 + 2 ^ r))
      = nu ^ ((1 + 2 ^ r) * (1 + 2 ^ s)) := by
    have h' := congrArg (· ^ ((1 + 2 ^ r) * (1 + 2 ^ s))) h
    simp only [mul_pow, ← pow_mul] at h'
    rw [show 2 ^ i * ((1 + 2 ^ r) * (1 + 2 ^ s))
          = (1 + 2 ^ r) * (2 ^ i * (1 + 2 ^ s)) by ring1,
      show 2 ^ j * ((1 + 2 ^ r) * (1 + 2 ^ s))
          = (1 + 2 ^ s) * (2 ^ j * (1 + 2 ^ r)) by ring1,
      pow_mul lam (1 + 2 ^ r) (2 ^ i * (1 + 2 ^ s)),
      pow_mul mu (1 + 2 ^ s) (2 ^ j * (1 + 2 ^ r)),
      hlam, hmu, ← pow_add] at h'
    exact h'
  have hmod : 2 ^ i * (1 + 2 ^ s) + 2 ^ j * (1 + 2 ^ r)
      ≡ (1 + 2 ^ r) * (1 + 2 ^ s) [MOD 2 ^ n - 1] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp key
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  exact hcast

/-- **The two-powers-to-one eigenvalue bridge** (case `θ = φ = 1`, Higman
p. 90).  From `λ^{2^a + 2^b} = λ^{2^c}` for `λ` of order `2 ^ n - 1`, the
exponents agree mod `2 ^ n - 1`, in the form consumed by
`higman_two_pow_add_eq_two_pow`. -/
theorem higman_two_pow_add_congruence_of_pow_eq {F : Type*} [Monoid F] {lam : F}
    {n a b c : ℕ} (hn : 0 < n) (hord : orderOf lam = 2 ^ n - 1)
    (h : lam ^ (2 ^ a + 2 ^ b) = lam ^ 2 ^ c) :
    (2 : ZMod (2 ^ n - 1)) ^ a + 2 ^ b = 2 ^ c := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder lam := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmod : 2 ^ a + 2 ^ b ≡ 2 ^ c [MOD 2 ^ n - 1] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp h
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  exact hcast

/-- **The `s = ±r` eigenvalue bridge** (case `θ = φ ≠ 1`, Higman p. 91).
From `λ^{2^i (1 + 2^s)} = λ^{2^t (1 + 2^r)}` for `λ` of order `2 ^ n - 1`,
the exponents agree mod `2 ^ n - 1`, in the form consumed by
`higman_typeB_exponent_pm`. -/
theorem higman_typeB_congruence_of_pow_eq {F : Type*} [Monoid F] {lam : F}
    {n r s i t : ℕ} (hn : 0 < n) (hord : orderOf lam = 2 ^ n - 1)
    (h : lam ^ (2 ^ i * (1 + 2 ^ s)) = lam ^ (2 ^ t * (1 + 2 ^ r))) :
    (2 : ZMod (2 ^ n - 1)) ^ i * (1 + 2 ^ s) = 2 ^ t * (1 + 2 ^ r) := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder lam := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmod : 2 ^ i * (1 + 2 ^ s) ≡ 2 ^ t * (1 + 2 ^ r) [MOD 2 ^ n - 1] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp h
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  exact hcast

end OddOrder.Higman.Suzuki2Groups
