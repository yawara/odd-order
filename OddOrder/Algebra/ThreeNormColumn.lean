/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.SumSquaresFour

/-!
# An integer column of norm `3` orthogonal to the degrees

Navarro's proof of the `Z*`-theorem reaches, on p. 142, three integer columns `u_1, u_2, u_3`
indexed by `Irr(B_0(G))` with

* `(u_i, u_i) = 3`,
* first entry `1` (the entry at the trivial character),
* `(χ(1), u_i) = 0`, where `χ(1)` is the column of degrees.

He concludes that the nonzero entries of `u_i` are `{1, 1, -1}` in some order.  That deduction is
pure arithmetic and is what this file isolates: norm `3` with a known `±1` entry forces exactly
three nonzero entries, all `±1` (`SumSquaresFour`, generalised to totals `≤ 4`), and orthogonality
to a column of **positive** degrees with `χ_0(1) = 1` then fixes the signs — two `+1` and one `-1`
is the only possibility, because `1 = a + b` is unsolvable in degrees `≥ 1` and `1 + a + b = 0` is
unsolvable in positive integers.

The degree relation `deg j = 1 + deg i` that falls out is Navarro's `χ_c(1) = 1 + χ_b(1)`.

## Main results

* `OddOrder.Algebra.exists_pair_of_sum_sq_eq_three`
-/

namespace OddOrder.Algebra

open Finset

variable {S : Type*} [Fintype S] {u deg : S → ℤ} {i₀ : S}

/-- **Navarro p. 142**: an integer column of norm `3` whose entry at `i₀` is `1`, orthogonal to a
column of degrees that are all at least `1` and equal `1` at `i₀`, has exactly three nonzero
entries: the one at `i₀`, a second `+1`, and a third `-1`.  The two extra indices satisfy
`deg j = 1 + deg i`. -/
theorem exists_pair_of_sum_sq_eq_three (hdeg0 : deg i₀ = 1) (hdegpos : ∀ k, 1 ≤ deg k)
    (hu0 : u i₀ = 1) (hsum : ∑ k, u k ^ 2 = 3) (horth : ∑ k, deg k * u k = 0) :
    ∃ i j : S, i ≠ i₀ ∧ j ≠ i₀ ∧ i ≠ j ∧ u i = 1 ∧ u j = -1 ∧ deg j = 1 + deg i ∧
      ∀ k : S, k ≠ i₀ → k ≠ i → k ≠ j → u k = 0 := by
  classical
  have hi₀sq : u i₀ ^ 2 = 1 := by rw [hu0]; norm_num
  -- the support has exactly three elements, one of which is `i₀`
  set T : Finset S := Finset.univ.filter fun k => u k ≠ 0 with hT
  have hcard : T.card = 3 :=
    card_filter_ne_zero_of_sum_sq_le_four (n := 3) (by norm_num) (by exact_mod_cast hsum) hi₀sq
  have hi₀T : i₀ ∈ T := mem_filter.mpr ⟨mem_univ _, by rw [hu0]; norm_num⟩
  have herase : (T.erase i₀).card = 2 := by rw [card_erase_of_mem hi₀T, hcard]
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp herase
  have hiT : i ∈ T := mem_of_mem_erase (hpair ▸ mem_insert_self i {j})
  have hjT : j ∈ T := mem_of_mem_erase (hpair ▸ mem_insert_of_mem (mem_singleton_self j))
  have hii₀ : i ≠ i₀ := ne_of_mem_erase (hpair ▸ mem_insert_self i {j})
  have hji₀ : j ≠ i₀ := ne_of_mem_erase (hpair ▸ mem_insert_of_mem (mem_singleton_self j))
  -- off the support the entries vanish, and on it they are `±1`
  have hoff : ∀ k : S, k ≠ i₀ → k ≠ i → k ≠ j → u k = 0 := by
    intro k hk0 hki hkj
    by_contra hk
    have hkT : k ∈ T := mem_filter.mpr ⟨mem_univ _, hk⟩
    have : k ∈ T.erase i₀ := mem_erase.mpr ⟨hk0, hkT⟩
    rw [hpair] at this
    rcases mem_insert.mp this with h | h
    · exact hki h
    · exact hkj (mem_singleton.mp h)
  have hpm : ∀ k : S, u k ≠ 0 → u k = 1 ∨ u k = -1 := fun k hk =>
    (eq_zero_or_one_or_neg_one_of_sum_sq_le_four (n := 3) (by norm_num) hsum hi₀sq k).resolve_left
      hk
  have hiv := hpm i (mem_filter.mp hiT).2
  have hjv := hpm j (mem_filter.mp hjT).2
  -- the orthogonality relation, read on the three surviving indices
  have hzero_off : ∀ k ∈ Finset.univ, k ∉ (insert i₀ {i, j} : Finset S) → deg k * u k = 0 := by
    intro k _ hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    rw [hoff k hk.1 hk.2.1 hk.2.2, mul_zero]
  have hnotmem : i₀ ∉ ({i, j} : Finset S) := by
    simp only [mem_insert, mem_singleton]
    exact fun h => h.elim (fun h => hii₀ h.symm) fun h => hji₀ h.symm
  have hsub : ∑ k, deg k * u k = deg i₀ * u i₀ + (deg i * u i + deg j * u j) := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert i₀ {i, j} : Finset S)) hzero_off,
      Finset.sum_insert hnotmem, Finset.sum_pair hij]
  rw [hsub, hu0, hdeg0, mul_one] at horth
  have hdi := hdegpos i
  have hdj := hdegpos j
  -- both signs positive or both negative is impossible; the mixed case gives the degree relation
  rcases hiv with hiv | hiv <;> rcases hjv with hjv | hjv <;>
    rw [hiv, hjv] at horth
  · exact absurd horth (by omega)
  · exact ⟨i, j, hii₀, hji₀, hij, hiv, hjv, by omega, hoff⟩
  · exact ⟨j, i, hji₀, hii₀, hij.symm, hjv, hiv, by omega,
      fun k hk0 hkj hki => hoff k hk0 hki hkj⟩
  · exact absurd horth (by omega)

end OddOrder.Algebra
