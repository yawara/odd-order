/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Tactic.LinearCombination
import OddOrder.Algebra.ThreeNormColumn

/-!
# Reading off the columns `D^t_j` — Navarro p. 143

On p. 142 Navarro fixes notation so that the first of the three half-sums has entries
`(u_1)_3 = (1, δ_1, δ_2)` with `δ_1 δ_2 = -1`, and shows `(u_2)_3 = (u_3)_3 = (1, 0, 0)`.  On
p. 143 he then reads the columns `D^t_j` off the identities

`D^t_1 = u_3 - u_1`,  `D^t_2 = u_2 - u_1`,  `D^t_0 = 2u_1 - D^y_0 + D^t_1 + D^t_2`

and arrives at the two sign relations

* (6) `1 + δ_1 χ_1(t) - δ_2 χ_2(t) = 0`,
* (7) `1 + δ_1 χ_1(1) + δ_2 χ_2(1) = 0`,

which `SignRelationSolution` then combines with (10) to finish the proof.

Both steps are integer-vector bookkeeping, and this file carries them with no representation
theory attached.  Navarro's two "choose notation" moves become explicit: the first is the *naming*
of the two extra support indices of `u_1` (so `δ_1, δ_2` are just its entries there), and the
second is a genuine case split on which of them carries the nonzero entry of `D^y_0`, resolved by
exchanging `(i, δ_1)` with `(j, δ_2)`.

## Main results

* `OddOrder.Algebra.eq_one_or_neg_one_of_mul_eq_neg_one` — `δ_1 δ_2 = -1` makes both `±1`
* `OddOrder.Algebra.eq_zero_of_dotProduct_eq_one` — `(u_2)_3 = (1, 0, 0)`
* `OddOrder.Algebra.sign_relation_six` — (6), once `D^y_0` vanishes at `j`
* `OddOrder.Algebra.exists_sign_relations` — (6) and (7) after the notation is chosen
-/

namespace OddOrder.Algebra

open Finset

variable {S : Type*} [Fintype S]

/-- Two integers whose product is `-1` are each `±1`. -/
theorem eq_one_or_neg_one_of_mul_eq_neg_one {δ₁ δ₂ : ℤ} (h : δ₁ * δ₂ = -1) :
    (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) := by
  have hnat : δ₁.natAbs * δ₂.natAbs = 1 := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs h
  have h1 : δ₁.natAbs = 1 := Nat.dvd_one.mp ⟨δ₂.natAbs, hnat.symm⟩
  have h2 : δ₂.natAbs = 1 := Nat.dvd_one.mp ⟨δ₁.natAbs, by rw [Nat.mul_comm]; exact hnat.symm⟩
  exact ⟨Int.natAbs_eq_iff.mp h1, Int.natAbs_eq_iff.mp h2⟩

/-- Two integers whose product is `-1` square to `1`. -/
theorem mul_self_eq_one_of_mul_eq_neg_one {δ₁ δ₂ : ℤ} (h : δ₁ * δ₂ = -1) :
    δ₁ * δ₁ = 1 ∧ δ₂ * δ₂ = 1 := by
  have hnat : δ₁.natAbs * δ₂.natAbs = 1 := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs h
  have h1 : δ₁.natAbs = 1 := Nat.dvd_one.mp ⟨δ₂.natAbs, hnat.symm⟩
  have h2 : δ₂.natAbs = 1 := Nat.dvd_one.mp ⟨δ₁.natAbs, by rw [Nat.mul_comm]; exact hnat.symm⟩
  refine ⟨?_, ?_⟩
  · rw [← Int.natAbs_mul_self, h1]; norm_num
  · rw [← Int.natAbs_mul_self, h2]; norm_num

/-- **Navarro p. 142, the shape of `u_2` and `u_3`.**  A column `v` of the same shape as `u`
— entry `1` at `i₀`, exactly one further `+1` and one further `-1` — that pairs to `1` with a
column `u` supported on `{i₀, i, j}` with entries `1, δ_1, δ_2` must vanish at `i` and at `j`.

`δ_1 δ_2 = -1` makes the pairing condition read `δ_1(v i - v j) = 0`, so `v i = v j`; and two
equal entries cannot be the `+1` and the `-1` of `v`, nor can they both be nonzero without
exhausting a support of size three that already contains `i₀`. -/
theorem eq_zero_of_dotProduct_eq_one {u v : S → ℤ} {i₀ i j : S} {δ₁ δ₂ : ℤ}
    (hii₀ : i ≠ i₀) (hji₀ : j ≠ i₀) (hij : i ≠ j) (hδ : δ₁ * δ₂ = -1)
    (hu0 : u i₀ = 1) (hui : u i = δ₁) (huj : u j = δ₂)
    (huoff : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → u k = 0)
    (hv0 : v i₀ = 1) {p q : S} (hpi₀ : p ≠ i₀) (hqi₀ : q ≠ i₀) (hpq : p ≠ q)
    (hvp : v p = 1) (hvq : v q = -1)
    (hvoff : ∀ k, k ≠ i₀ → k ≠ p → k ≠ q → v k = 0)
    (hdot : ∑ k, u k * v k = 1) :
    v i = 0 ∧ v j = 0 := by
  classical
  obtain ⟨hδ₁, hδ₂⟩ := mul_self_eq_one_of_mul_eq_neg_one hδ
  -- the pairing sees only `i₀, i, j`
  have hzero_off : ∀ k ∈ Finset.univ, k ∉ (insert i₀ {i, j} : Finset S) → u k * v k = 0 := by
    intro k _ hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    rw [huoff k hk.1 hk.2.1 hk.2.2, zero_mul]
  have hnotmem : i₀ ∉ ({i, j} : Finset S) := by
    simp only [mem_insert, mem_singleton]
    exact fun h => h.elim (fun h => hii₀ h.symm) fun h => hji₀ h.symm
  have hsub : ∑ k, u k * v k = u i₀ * v i₀ + (u i * v i + u j * v j) := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert i₀ {i, j} : Finset S)) hzero_off,
      Finset.sum_insert hnotmem, Finset.sum_pair hij]
  rw [hsub, hu0, hv0, hui, huj, mul_one] at hdot
  -- hence `v i = v j`
  have h0 : δ₁ * v i + δ₂ * v j = 0 := by linarith
  have heq : v i = v j := by linear_combination δ₁ * h0 - v i * hδ₁ - v j * hδ
  -- an entry outside `{p, q}` is zero, and `p`, `q` carry different values
  have hval : ∀ k : S, k ≠ i₀ → v k = 1 ∨ v k = -1 ∨ v k = 0 := by
    intro k hk
    by_cases hkp : k = p
    · exact Or.inl (hkp ▸ hvp)
    by_cases hkq : k = q
    · exact Or.inr (Or.inl (hkq ▸ hvq))
    exact Or.inr (Or.inr (hvoff k hk hkp hkq))
  have hvi : v i = 0 := by
    by_contra hvi
    -- `v i = v j ≠ 0` forces both `i` and `j` into `{p, q}`, which carry opposite values
    have hi : i = p ∨ i = q := by
      by_contra hc
      push Not at hc
      exact hvi (hvoff i hii₀ hc.1 hc.2)
    have hj : j = p ∨ j = q := by
      by_contra hc
      push Not at hc
      exact (heq ▸ hvi) (hvoff j hji₀ hc.1 hc.2)
    rcases hi with rfl | rfl <;> rcases hj with h | h
    · exact hij h.symm
    · rw [hvp, h, hvq] at heq; omega
    · rw [hvq, h, hvp] at heq; omega
    · exact hij h.symm
  exact ⟨hvi, heq ▸ hvi⟩

variable {a g T b c d u₁ u₂ u₃ : S → ℤ} {i₀ i j : S} {δ₁ δ₂ s₁ s₂ : ℤ}

omit [Fintype S] in
/-- **Navarro p. 143, relation (6).**  With `D^t_1 = u_3 - u_1`, `D^t_2 = u_2 - u_1` and
`D^t_0 = 2u_1 - D^y_0 + D^t_1 + D^t_2`, the column `χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2`
has `χ(t)_i = -a_i - δ_1(ψ_1(1) + ψ_2(1))` and `χ(t)_j = -δ_2(ψ_1(1) + ψ_2(1))`, so the
combination `1 + δ_1 χ(t)_i - δ_2 χ(t)_j` collapses to `1 - δ_1 a_i`, which is `0` by
`(D^y_0, u_1) = 2`. -/
theorem sign_relation_six (hδ : δ₁ * δ₂ = -1)
    (hu₁i : u₁ i = δ₁) (hu₁j : u₁ j = δ₂)
    (hu₂i : u₂ i = 0) (hu₂j : u₂ j = 0) (hu₃i : u₃ i = 0) (hu₃j : u₃ j = 0)
    (hc : ∀ k, c k = u₃ k - u₁ k) (hd : ∀ k, d k = u₂ k - u₁ k)
    (hb : ∀ k, 2 * u₁ k = a k + b k - c k - d k)
    (hTi : T i = b i + s₁ * c i + s₂ * d i) (hTj : T j = b j + s₁ * c j + s₂ * d j)
    (haj : a j = 0) (hau : 1 + δ₁ * a i + δ₂ * a j = 2) :
    1 + δ₁ * T i - δ₂ * T j = 0 := by
  obtain ⟨hδ₁, hδ₂⟩ := mul_self_eq_one_of_mul_eq_neg_one hδ
  have hci : c i = -δ₁ := by rw [hc i, hu₃i, hu₁i]; ring
  have hcj : c j = -δ₂ := by rw [hc j, hu₃j, hu₁j]; ring
  have hdi : d i = -δ₁ := by rw [hd i, hu₂i, hu₁i]; ring
  have hdj : d j = -δ₂ := by rw [hd j, hu₂j, hu₁j]; ring
  have hbi : b i = -a i := by have := hb i; rw [hu₁i, hci, hdi] at this; linarith
  have hbj : b j = 0 := by have := hb j; rw [hu₁j, hcj, hdj, haj] at this; linarith
  have hTi' : T i = -a i - δ₁ * (s₁ + s₂) := by rw [hTi, hbi, hci, hdi]; ring
  have hTj' : T j = -δ₂ * (s₁ + s₂) := by rw [hTj, hbj, hcj, hdj]; ring
  rw [haj, mul_zero, add_zero] at hau
  rw [hTi', hTj']
  linear_combination (-1 : ℤ) * hau - (s₁ + s₂) * hδ₁ + (s₁ + s₂) * hδ₂

omit [Fintype S] in
/-- **Navarro p. 143, both sign relations, with the notation chosen.**

`(D^y_0, u_1) = 2` reads `δ_1 a_i + δ_2 a_j = 1`, and `δ_2 = -δ_1`, so `a_i - a_j = δ_1`; since
the entries of `D^y_0` are `0, ±1` this leaves `(a_i, a_j) = (δ_1, 0)` or `(0, δ_2)`.  Navarro
disposes of the second case by "interchanging the second and the third rows"; here that is the
exchange of `(i, δ_1)` with `(j, δ_2)`, under which every hypothesis is symmetric.

The output is exactly the pair `(6)`, `(7)` that `eq_of_sign_relations` consumes, together with
the record of *which* of the two namings was taken — every other fact about the pair (Navarro's
(10), or that the indices avoid the trivial character) is symmetric in the exchange and transfers
along that disjunction. -/
theorem exists_sign_relations (hδ : δ₁ * δ₂ = -1)
    (hu₁i : u₁ i = δ₁) (hu₁j : u₁ j = δ₂)
    (hu₂i : u₂ i = 0) (hu₂j : u₂ j = 0) (hu₃i : u₃ i = 0) (hu₃j : u₃ j = 0)
    (hc : ∀ k, c k = u₃ k - u₁ k) (hd : ∀ k, d k = u₂ k - u₁ k)
    (hb : ∀ k, 2 * u₁ k = a k + b k - c k - d k)
    (hTi : T i = b i + s₁ * c i + s₂ * d i) (hTj : T j = b j + s₁ * c j + s₂ * d j)
    (hai' : a i = 0 ∨ a i = 1 ∨ a i = -1) (haj' : a j = 0 ∨ a j = 1 ∨ a j = -1)
    (hau : 1 + δ₁ * a i + δ₂ * a j = 2)
    (hg : 1 + δ₁ * g i + δ₂ * g j = 0) :
    ∃ (i' j' : S) (e₁ e₂ : ℤ),
      ((i' = i ∧ j' = j ∧ e₁ = δ₁ ∧ e₂ = δ₂) ∨ (i' = j ∧ j' = i ∧ e₁ = δ₂ ∧ e₂ = δ₁)) ∧
      e₁ * e₂ = -1 ∧ 1 + e₁ * T i' - e₂ * T j' = 0 ∧ 1 + e₁ * g i' + e₂ * g j' = 0 := by
  obtain ⟨hδ₁, hδ₂⟩ := mul_self_eq_one_of_mul_eq_neg_one hδ
  obtain ⟨h₁, h₂⟩ := eq_one_or_neg_one_of_mul_eq_neg_one hδ
  -- `δ_2 = -δ_1`, so `(D^y_0, u_1) = 2` says `a_i - a_j = δ_1`
  have hneg : δ₂ = -δ₁ := by linear_combination δ₁ * hδ - δ₂ * hδ₁
  have hsub : a i - a j = δ₁ := by
    rw [hneg] at hau
    linear_combination δ₁ * hau - (a i - a j) * hδ₁
  have hcase : a j = 0 ∨ a i = 0 := by
    rcases h₁ with rfl | rfl <;> rcases hai' with h | h | h <;> rcases haj' with h' | h' | h' <;>
      omega
  rcases hcase with hz | hz
  · exact ⟨i, j, δ₁, δ₂, Or.inl ⟨rfl, rfl, rfl, rfl⟩, hδ,
      sign_relation_six hδ hu₁i hu₁j hu₂i hu₂j hu₃i hu₃j hc hd hb hTi hTj hz hau, hg⟩
  · refine ⟨j, i, δ₂, δ₁, Or.inr ⟨rfl, rfl, rfl, rfl⟩, by linarith [hδ, mul_comm δ₁ δ₂],
      sign_relation_six (by rw [mul_comm]; exact hδ) hu₁j hu₁i hu₂j hu₂i hu₃j hu₃i hc hd hb hTj hTi
        hz (by linarith), by linarith⟩

end OddOrder.Algebra
