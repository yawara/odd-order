/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BasicSetColumnShape
import OddOrder.Algebra.HalfSumColumns
import OddOrder.Algebra.SignRelationSolution

/-!
# The endgame of Brauer–Suzuki, assembled — Navarro pp. 142–145

Pages 142–145 of Navarro's proof are, once the representation theory has produced the four columns

`a = D^y_0`,  `b, c, d = D^t_0, D^t_1, D^t_2`,  `g = χ(1)`,  `T = χ(t)`

indexed by `Irr(B_0(G))`, a single computation with integer vectors.  This file runs it end to
end and returns Navarro's objective: **a nontrivial `χ ∈ Irr(B_0)` with `χ(t) = χ(1)`**, whose
kernel is the proper normal subgroup containing `t`.

The chain is

1. `dotProduct_of_halfSum` / `dotProduct_degree_of_halfSum` (p. 142) — the three half-sums
   `2u_1 = a + b - c - d`, `2u_2 = a + b - c + d`, `2u_3 = a + b + c - d` pair as
   `(u_i, u_j) = 1 + 2δ_ij`, are orthogonal to the degrees, and pair to `2` with `a`;
2. `exists_pair_of_sum_sq_eq_three` (p. 142) — norm `3` plus `u_i(i₀) = 1` and orthogonality to
   the degrees forces exactly three nonzero entries `1, 1, -1`;
3. `eq_zero_of_dotProduct_eq_one` (p. 142) — `u_2` and `u_3` vanish where `u_1` is `±1`;
4. `exists_sign_relations` (p. 143) — the relations (6) and (7), with the naming chosen;
5. `sign_relation_ten` (p. 145) — Burnside's `(u_1, Θ) = 0` becomes (10);
6. `eq_of_sign_relations` (p. 145) — (6), (7), (10) force `χ_1(t) = χ_1(1)`.

Step 5 is stated over an arbitrary domain because Navarro's `Θ_χ = χ(t)²/χ(1)` is carried without
division as `w_χ = ω_χ(K̂)² χ(1)`, which lives in the splitting field, not in `ℤ`; the resulting
relation (10) is an identity between integers again.

## Main results

* `OddOrder.Algebra.sign_relation_ten` — `(w, u_1) = 0` becomes Navarro's (10)
* `OddOrder.Algebra.exists_halfSum_columns` — the half-sums exist over `ℤ`
* `OddOrder.Algebra.exists_eq_of_columns` — the whole endgame
* `OddOrder.Algebra.exists_eq_of_columns_of_odd_degrees` — the same, from textbook inputs only
-/

namespace OddOrder.Algebra

open Finset

variable {S : Type*} [Fintype S]

/-! ### Reading a pairing off a column with three-element support -/

/-- A pairing against a column supported on `{i₀, i, j}` sees only those three entries. -/
theorem sum_mul_eq_of_support {R : Type*} [CommRing R] {v u : S → R} {i₀ i j : S}
    (hii₀ : i ≠ i₀) (hji₀ : j ≠ i₀) (hij : i ≠ j)
    (hoff : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → u k = 0) :
    ∑ k, v k * u k = v i₀ * u i₀ + (v i * u i + v j * u j) := by
  classical
  have hzero_off : ∀ k ∈ (Finset.univ : Finset S), k ∉ (insert i₀ {i, j} : Finset S) →
      v k * u k = 0 := by
    intro k _ hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    rw [hoff k hk.1 hk.2.1 hk.2.2, mul_zero]
  have hnotmem : i₀ ∉ ({i, j} : Finset S) := by
    simp only [mem_insert, mem_singleton]
    exact fun h => h.elim (fun h => hii₀ h.symm) fun h => hji₀ h.symm
  rw [← Finset.sum_subset (Finset.subset_univ (insert i₀ {i, j} : Finset S)) hzero_off,
    Finset.sum_insert hnotmem, Finset.sum_pair hij]

/-! ### Navarro (9) ⟹ (10) -/

/-- **Navarro p. 145, relation (10).**  Burnside's step gives a family `w` orthogonal to the
column `u_1`; Navarro's `Θ_χ = χ(t)²/χ(1)` is `w` divided by the fixed constant `m = |cl(t)|²`,
and `w_χ χ(1) = m χ(t)²` is the division-free form of that.  Multiplying
`m + δ_1 w_i + δ_2 w_j = 0` by `χ_i(1) χ_j(1)` and cancelling `m` gives

`χ_i(1) χ_j(1) + δ_1 χ_i(t)² χ_j(1) + δ_2 χ_j(t)² χ_i(1) = 0`.

The value of `w` at the trivial character is `m` itself, since `1_G(t)² = 1_G(1) = 1`. -/
theorem sign_relation_ten {R : Type*} [CommRing R] [IsDomain R] {w g T u : S → R} {m δ₁ δ₂ : R}
    {i₀ i j : S} (hm : m ≠ 0) (hii₀ : i ≠ i₀) (hji₀ : j ≠ i₀) (hij : i ≠ j)
    (hwg : ∀ k, w k * g k = m * T k ^ 2) (hwi₀ : w i₀ = m)
    (hu0 : u i₀ = 1) (hui : u i = δ₁) (huj : u j = δ₂)
    (huoff : ∀ k, k ≠ i₀ → k ≠ i → k ≠ j → u k = 0)
    (hzero : ∑ k, w k * u k = 0) :
    g i * g j + δ₁ * T i ^ 2 * g j + δ₂ * T j ^ 2 * g i = 0 := by
  rw [sum_mul_eq_of_support hii₀ hji₀ hij huoff, hu0, hui, huj, hwi₀, mul_one] at hzero
  refine mul_left_cancel₀ hm ?_
  rw [mul_zero]
  calc m * (g i * g j + δ₁ * T i ^ 2 * g j + δ₂ * T j ^ 2 * g i)
      = (g i * g j) * m + (w i * g i) * (δ₁ * g j) + (w j * g j) * (δ₂ * g i) := by
        rw [hwg i, hwg j]; ring
    _ = (m + (w i * δ₁ + w j * δ₂)) * (g i * g j) := by ring
    _ = 0 := by rw [hzero, zero_mul]

/-! ### The half-sums are integer columns -/

omit [Fintype S] in
/-- **The four columns are congruent mod `2`.**  Navarro's inputs are `χ(t) ≡ χ(y) mod 2` and that
the basic-set degrees `ψ_1(1), ψ_2(1)` are odd; since `χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2`,
the second turns `χ(t)` into `D^t_0 + D^t_1 + D^t_2` mod `2`. -/
theorem two_dvd_sum_of_odd_degrees {a b c d T : S → ℤ} {s₁ s₂ : ℤ} (hs₁ : Odd s₁) (hs₂ : Odd s₂)
    (hT : ∀ k, T k = b k + s₁ * c k + s₂ * d k) (hcong : ∀ k, (2 : ℤ) ∣ (a k + T k)) (k : S) :
    (2 : ℤ) ∣ (a k + b k + c k + d k) := by
  obtain ⟨r, hr⟩ := hs₁
  obtain ⟨q, hq⟩ := hs₂
  obtain ⟨m, hm⟩ := hcong k
  refine ⟨m - r * c k - q * d k, ?_⟩
  have hTk := hT k
  rw [hr, hq] at hTk
  linarith [hm, hTk]

omit [Fintype S] in
/-- **The three half-sums of Navarro p. 142 exist as integer columns.**  Each of
`a + b − c − d`, `a + b − c + d`, `a + b + c − d` differs from `a + b + c + d` by twice an integer
column, so the single congruence `2 ∣ a + b + c + d` produces all three. -/
theorem exists_halfSum_columns {a b c d : S → ℤ}
    (h : ∀ k, (2 : ℤ) ∣ (a k + b k + c k + d k)) :
    ∃ u₁ u₂ u₃ : S → ℤ,
      (∀ k, 2 * u₁ k = a k + b k - c k - d k) ∧
      (∀ k, 2 * u₂ k = a k + b k - c k + d k) ∧
      (∀ k, 2 * u₃ k = a k + b k + c k - d k) := by
  choose m hm using h
  refine ⟨fun k => m k - c k - d k, fun k => m k - c k, fun k => m k - d k,
    fun k => ?_, fun k => ?_, fun k => ?_⟩ <;> linarith [hm k]

/-! ### The whole endgame -/

omit [Fintype S] in
/-- The three half-sums take the value `1` at the trivial character. -/
private theorem halfSum_eq_one {a b c d v : S → ℤ} {i₀ : S} {εc εd : ℤ}
    (hv : ∀ k, 2 * v k = a k + b k + εc * c k + εd * d k)
    (ha0 : a i₀ = 1) (hb0 : b i₀ = 1) (hc0 : c i₀ = 0) (hd0 : d i₀ = 0) : v i₀ = 1 := by
  have h := hv i₀
  rw [ha0, hb0, hc0, hd0, mul_zero, mul_zero] at h
  omega

variable {a b c d g T u₁ u₂ u₃ : S → ℤ} {i₀ : S} {s₁ s₂ : ℤ}

/-- **Navarro pp. 142–145.**  From the pairing table of the four columns of the "analysis at `y`"
and the "analysis at `t`", their values at the trivial character, the expansion
`χ(t) = D^t_0 + ψ_1(1) D^t_1 + ψ_2(1) D^t_2`, and Burnside's relation (10), one gets a
**nontrivial** irreducible character of the principal block with `χ(t) = χ(1)` — Navarro's
objective on p. 139.

`h10` is asked for at whichever pair of indices carries the two extra `±1` entries of `u_1`; the
supplier is `sign_relation_ten`. -/
theorem exists_eq_of_columns
    (haa : ∑ k, a k * a k = 4) (hbb : ∑ k, b k * b k = 4) (hcc : ∑ k, c k * c k = 4)
    (hdd : ∑ k, d k * d k = 4) (hab : ∑ k, a k * b k = 0) (hac : ∑ k, a k * c k = 0)
    (had : ∑ k, a k * d k = 0) (hbc : ∑ k, b k * c k = 2) (hbd : ∑ k, b k * d k = 2)
    (hcd : ∑ k, c k * d k = 2)
    (hga : ∑ k, g k * a k = 0) (hgb : ∑ k, g k * b k = 0) (hgc : ∑ k, g k * c k = 0)
    (hgd : ∑ k, g k * d k = 0)
    (hv₁ : ∀ k, 2 * u₁ k = a k + b k - c k - d k)
    (hv₂ : ∀ k, 2 * u₂ k = a k + b k - c k + d k)
    (hv₃ : ∀ k, 2 * u₃ k = a k + b k + c k - d k)
    (hg0 : g i₀ = 1) (hgpos : ∀ k, 1 ≤ g k)
    (ha0 : a i₀ = 1) (hb0 : b i₀ = 1) (hc0 : c i₀ = 0) (hd0 : d i₀ = 0)
    (hT : ∀ k, T k = b k + s₁ * c k + s₂ * d k)
    (h10 : ∀ i j : S, i ≠ i₀ → j ≠ i₀ → i ≠ j → u₁ i = 1 → u₁ j = -1 →
      (∀ k, k ≠ i₀ → k ≠ i → k ≠ j → u₁ k = 0) →
      g i * g j + T i ^ 2 * g j - T j ^ 2 * g i = 0) :
    ∃ k : S, k ≠ i₀ ∧ g k = T k := by
  classical
  -- the sign patterns, as `HalfSumColumns` wants them
  have hs₁ : ∀ k, 2 * u₁ k = a k + b k + (-1) * c k + (-1) * d k := fun k => by
    rw [hv₁ k]; ring
  have hs₂ : ∀ k, 2 * u₂ k = a k + b k + (-1) * c k + 1 * d k := fun k => by rw [hv₂ k]; ring
  have hs₃ : ∀ k, 2 * u₃ k = a k + b k + 1 * c k + (-1) * d k := fun k => by rw [hv₃ k]; ring
  have hu₁0 : u₁ i₀ = 1 := halfSum_eq_one hs₁ ha0 hb0 hc0 hd0
  have hu₂0 : u₂ i₀ = 1 := halfSum_eq_one hs₂ ha0 hb0 hc0 hd0
  have hu₃0 : u₃ i₀ = 1 := halfSum_eq_one hs₃ ha0 hb0 hc0 hd0
  -- the pairing table of the three half-sums
  obtain ⟨hpair, hapair⟩ := dotProduct_of_halfSum haa hbb hcc hdd hab hac had hbc hbd hcd
    (u := ![u₁, u₂, u₃]) hv₁ hv₂ hv₃
  have hgpair := dotProduct_degree_of_halfSum hga hgb hgc hgd
    (u := ![u₁, u₂, u₃]) hv₁ hv₂ hv₃
  -- the three columns have norm `3`, entry `1` at `i₀`, and are orthogonal to the degrees
  have hshape : ∀ (v : S → ℤ) (r : Fin 3), (∀ k, v k = ![u₁, u₂, u₃] r k) → v i₀ = 1 →
      ∃ i j : S, i ≠ i₀ ∧ j ≠ i₀ ∧ i ≠ j ∧ v i = 1 ∧ v j = -1 ∧ g j = 1 + g i ∧
        ∀ k : S, k ≠ i₀ → k ≠ i → k ≠ j → v k = 0 := by
    intro v r hvr hv0
    refine exists_pair_of_sum_sq_eq_three hg0 hgpos hv0 ?_ ?_
    · rw [Finset.sum_congr rfl fun k _ => by rw [hvr k, sq], hpair r r, if_pos rfl]
      norm_num
    · rw [Finset.sum_congr rfl fun k _ => by rw [hvr k], hgpair r]
  obtain ⟨i, j, hii₀, hji₀, hij, hu₁i, hu₁j, hgj, hu₁off⟩ :=
    hshape u₁ 0 (fun _ => rfl) hu₁0
  obtain ⟨p₂, q₂, hp₂, hq₂, hpq₂, hvp₂, hvq₂, -, hoff₂⟩ := hshape u₂ 1 (fun _ => rfl) hu₂0
  obtain ⟨p₃, q₃, hp₃, hq₃, hpq₃, hvp₃, hvq₃, -, hoff₃⟩ := hshape u₃ 2 (fun _ => rfl) hu₃0
  have hδ : (1 : ℤ) * (-1) = -1 := by norm_num
  -- `u_2` and `u_3` vanish at `i` and `j`
  obtain ⟨hu₂i, hu₂j⟩ := eq_zero_of_dotProduct_eq_one hii₀ hji₀ hij hδ hu₁0 hu₁i hu₁j hu₁off
    hu₂0 hp₂ hq₂ hpq₂ hvp₂ hvq₂ hoff₂
    (by rw [Finset.sum_congr rfl fun k _ => rfl]; simpa using hpair 0 1)
  obtain ⟨hu₃i, hu₃j⟩ := eq_zero_of_dotProduct_eq_one hii₀ hji₀ hij hδ hu₁0 hu₁i hu₁j hu₁off
    hu₃0 hp₃ hq₃ hpq₃ hvp₃ hvq₃ hoff₃
    (by rw [Finset.sum_congr rfl fun k _ => rfl]; simpa using hpair 0 2)
  -- the two pairings against `u_1`, read on its three-element support
  have hau : 1 + 1 * a i + (-1) * a j = 2 := by
    have h := hapair 0
    rw [show (∑ k, a k * ![u₁, u₂, u₃] 0 k) = ∑ k, a k * u₁ k from rfl,
      sum_mul_eq_of_support hii₀ hji₀ hij hu₁off, hu₁0, hu₁i, hu₁j, ha0] at h
    linarith
  have hgu : 1 + 1 * g i + (-1) * g j = 0 := by
    have h := hgpair 0
    rw [show (∑ k, g k * ![u₁, u₂, u₃] 0 k) = ∑ k, g k * u₁ k from rfl,
      sum_mul_eq_of_support hii₀ hji₀ hij hu₁off, hu₁0, hu₁i, hu₁j, hg0] at h
    linarith
  -- the entries of `a` are `0, ±1`
  have hasq : ∑ k, a k ^ 2 = 4 := by
    rw [Finset.sum_congr rfl fun k _ => sq (a k)]; exact haa
  have hai₀ : a i₀ ^ 2 = 1 := by rw [ha0]; norm_num
  have hai' := eq_zero_or_one_or_neg_one_of_sum_sq_le_four (le_refl 4) hasq hai₀ i
  have haj' := eq_zero_or_one_or_neg_one_of_sum_sq_le_four (le_refl 4) hasq hai₀ j
  -- `c = u_3 - u_1` and `d = u_2 - u_1`
  have hcu : ∀ k, c k = u₃ k - u₁ k := fun k => by
    have h₁ := hv₁ k; have h₃ := hv₃ k; omega
  have hdu : ∀ k, d k = u₂ k - u₁ k := fun k => by
    have h₁ := hv₁ k; have h₂ := hv₂ k; omega
  -- the sign relations (6), (7), with the naming chosen
  obtain ⟨i', j', e₁, e₂, hnaming, he, h6, h7⟩ :=
    exists_sign_relations hδ hu₁i hu₁j hu₂i hu₂j hu₃i hu₃j hcu hdu hv₁ hT hai' haj' hau hgu
  obtain ⟨he₁, he₂⟩ := mul_self_eq_one_of_mul_eq_neg_one he
  have hten := h10 i j hii₀ hji₀ hij hu₁i hu₁j hu₁off
  -- (10) at the chosen naming, and the substitution
  refine ⟨i', ?_, eq_of_sign_relations he₁ he₂ h6 h7 ?_⟩
  · rcases hnaming with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩
    · exact hii₀
    · exact hji₀
  · rcases hnaming with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> linarith [hten]

/-- **Navarro pp. 142–145, from the textbook inputs only.**  The three half-sums are not asked for
as data: they are produced from the single congruence `χ(t) ≡ χ(y) mod 2` together with the
oddness of the basic-set degrees (`two_dvd_sum_of_odd_degrees`, `exists_halfSum_columns`).

This is the form the "analysis at `t`" supplies: every hypothesis is a statement about the four
columns, the degrees and `χ(t)`, with no auxiliary column to construct by hand.  `h10` is
quantified over the half-sum because its supplier — Burnside's relation (9) halved — works for any
column with that defining equation. -/
theorem exists_eq_of_columns_of_odd_degrees
    (haa : ∑ k, a k * a k = 4) (hbb : ∑ k, b k * b k = 4) (hcc : ∑ k, c k * c k = 4)
    (hdd : ∑ k, d k * d k = 4) (hab : ∑ k, a k * b k = 0) (hac : ∑ k, a k * c k = 0)
    (had : ∑ k, a k * d k = 0) (hbc : ∑ k, b k * c k = 2) (hbd : ∑ k, b k * d k = 2)
    (hcd : ∑ k, c k * d k = 2)
    (hga : ∑ k, g k * a k = 0) (hgb : ∑ k, g k * b k = 0) (hgc : ∑ k, g k * c k = 0)
    (hgd : ∑ k, g k * d k = 0)
    (hg0 : g i₀ = 1) (hgpos : ∀ k, 1 ≤ g k)
    (ha0 : a i₀ = 1) (hb0 : b i₀ = 1) (hc0 : c i₀ = 0) (hd0 : d i₀ = 0)
    (hT : ∀ k, T k = b k + s₁ * c k + s₂ * d k) (hs₁ : Odd s₁) (hs₂ : Odd s₂)
    (hcong : ∀ k, (2 : ℤ) ∣ (a k + T k))
    (h10 : ∀ v : S → ℤ, (∀ k, 2 * v k = a k + b k - c k - d k) →
      ∀ i j : S, i ≠ i₀ → j ≠ i₀ → i ≠ j → v i = 1 → v j = -1 →
        (∀ k, k ≠ i₀ → k ≠ i → k ≠ j → v k = 0) →
        g i * g j + T i ^ 2 * g j - T j ^ 2 * g i = 0) :
    ∃ k : S, k ≠ i₀ ∧ g k = T k := by
  obtain ⟨v₁, v₂, v₃, hh₁, hh₂, hh₃⟩ :=
    exists_halfSum_columns (two_dvd_sum_of_odd_degrees hs₁ hs₂ hT hcong)
  exact exists_eq_of_columns haa hbb hcc hdd hab hac had hbc hbd hcd hga hgb hgc hgd hh₁ hh₂ hh₃
    hg0 hgpos ha0 hb0 hc0 hd0 hT (h10 v₁ hh₁)

end OddOrder.Algebra
