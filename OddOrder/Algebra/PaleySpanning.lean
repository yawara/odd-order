/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Paley-type spanning set of BG Appendix C, Problem 1

For a finite field `F` of characteristic three with `|F| ≡ 3 (mod 4)` — e.g. `F = 𝔽_{3^q}` with
`q` an odd prime — the *Paley set*

`T = { a ∈ F : a and a + 1 are both nonzero squares }`

generates `F` as an additive group.  This is **Lemma B** of
`notes/bg/appC_problem1_partial_resolution.md` (issue 0180): it is the one remaining hypothesis of
Theorem 1 there, and under the identification of `σ(P)` with `𝔽_{3^q}` it is exactly the spanning
hypothesis `hspan` of `OddOrder.BG.AppC.Problem1.false_of_centralizing_of_spanning`.

## The proof

The set `T` is *large* and *asymmetric*, and those two facts alone suffice.

* **Large.**  `u ↦ (u - u⁻¹)²` maps every unit with `u² ≠ 1` into `T`: it is a nonzero square,
  and in characteristic three `(u - u⁻¹)² + 1 = (u + u⁻¹)²` is a square as well, nonzero because
  `-1` is not a square.  Its fibres have at most four points (`u`, `-u`, `u⁻¹`, `-u⁻¹`), so
  `4|T| ≥ |F| - 3`.
* **Asymmetric.**  `T ∩ (-T) = ∅`, again because `-1` is not a square.  So the additive closure
  `A` of `T` contains the `2|T|` distinct elements of `T ∪ (-T)`.
* **Conclusion.**  A proper additive subgroup of `F` has index divisible by three, so
  `3 · |A| ≤ |F|`.  Combining, `6|T| ≤ |F| ≤ 4|T| + 3`, forcing `|T| ≤ 1` and hence `|F| ≤ 7`.

Note what is *not* needed: no Weil bound (the character-sum route to the same statement needs
one), no Galois module theory, and no separate treatment of `q = 3`.

## Main results

* `paleySet` — the set `T`.
* `card_paleySet_lower` — `|F| - 3 ≤ 4 |T|`, via the parametrisation `u ↦ (u - u⁻¹)²`.
* `isSquare_or_isSquare_neg` — every non-zero element is `±` a square.
* `addClosure_paleySet_eq_top` — **Lemma B**: `T` generates `(F, +)`.

## The automatic collision of `a ↦ (a+1)^E - a^E`

The second half of the file records why the Paley set is also the *obstruction* in BG Appendix C,
Problem 1.  For odd `E` the "discrete derivative" `powDiff E a = (a+1)^E - a^E` has a free
2-to-1 symmetry, the involution `a ↦ -a-1` (`powDiff_neg_sub_one`).  That involution maps `T`
into its complement whenever `-1` is a non-square (`neg_sub_one_notMem_paleySet`), so the
collisions that the trace criterion of
`OddOrder.BG.AppC.Problem1.false_of_collisionPair_trace_ne_zero` consumes — two *Paley* points
with the same `powDiff` — are never the automatic ones.  This is exactly the reason the general
`q` case of that criterion is hard, and it corrects the "`{(u, u^E)}` is a Sidon set" reading of
the problem: that graph is symmetric, hence never Sidon.

* `powDiff` — `a ↦ (a+1)^E - a^E`.
* `powDiff_neg_sub_one` — the free involution.
* `neg_sub_one_notMem_paleySet` — it always leaves `T`.
* `exists_paley_collision_pow_mul` — the `E` and `E²` collision problems are conjugate, so a
  usable collision for one gives one for the other.
* `exists_paley_collision_of_pow_eq` — the search-free certificate: two nonzero squares `t`, `t'`
  fixed by `z ↦ z ^ E` whose values `(1 - t) / (1 - t)^E` agree produce a collision outright.
* `isSquare_one_sub_inv_iff` — the inversion pairing: of `t` and `t⁻¹` exactly one is usable.
* `two_mul_card_usable_add_one` — exactly half of the fixed nonzero squares are usable.
* `card_image_mul_card_le` / `card_values_mul_card_le` — the index bound `|V| · |L| ≤ |U|`.
* `exists_sameCoset_pair_of_card_lt` / `exists_sameCoset_pair_of_card` /
  `exists_sameCoset_pair_of_card_arith` — **Theorem A**: `|L| (|L| - 1) > 2 |U|` gives two Paley
  points in one coset.
* `two_dvd_card_trivial_fibre` / `exists_sameCoset_pair_of_two_mul_card_le` — the parity
  refinement, which sharpens the criterion by one unit to `2 |V| ≤ |L|`.
* `notMem_prime_field_of_mem_paleySet` — the Paley set avoids `𝔽₃`.
* `exists_paley_collision_of_pow_char` — **one Paley point** whose collision value lies in `𝔽₃`
  already collides, namely with its own cube.
* `exists_paley_collision_of_pow_add` — **one Paley point** at which `z ↦ z ^ E` is additive on
  `(a, 1)` collides with its own inverse.
-/

namespace OddOrder.Paley

open Finset

variable {F : Type*} [Field F]

/-- **The Paley set** of a finite field: those `a` for which both `a` and `a + 1` are nonzero
squares.  For `F = 𝔽_{3^q}` the nonzero squares are the norm-one elements, so this is the set `T`
of BG Appendix C, Problem 1 (`notes/bg/appC_problem1_partial_resolution.md`). -/
def paleySet (F : Type*) [Field F] : Set F :=
  {a | a ≠ 0 ∧ IsSquare a ∧ a + 1 ≠ 0 ∧ IsSquare (a + 1)}

theorem mem_paleySet {a : F} :
    a ∈ paleySet F ↔ a ≠ 0 ∧ IsSquare a ∧ a + 1 ≠ 0 ∧ IsSquare (a + 1) := Iff.rfl

/-- `-1` is not a square when `|F| ≡ 3 (mod 4)`: Euler's criterion turns it into
`(-1)^{(|F|-1)/2}`, and that exponent is odd. -/
theorem not_isSquare_neg_one [Fintype F] (h2 : ringChar F ≠ 2) (h4 : Fintype.card F % 4 = 3) :
    ¬ IsSquare (-1 : F) := by
  have hne : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [FiniteField.isSquare_iff h2 hne]
  have hodd : Odd (Fintype.card F / 2) := Nat.odd_iff.mpr (by omega)
  rw [hodd.neg_one_pow]
  intro h
  have h20 : (2 : F) = 0 := by linear_combination -h
  have hdvd : ringChar F ∣ 2 := ringChar.dvd (by exact_mod_cast h20)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact h2 h1

/-- When `|F| ≡ 3 (mod 4)` the non-squares are exactly the negatives of the squares: every non-zero
element is `±` a square.  (Euler's criterion again: `(-1)^{(|F|-1)/2} = -1`.) -/
theorem isSquare_or_isSquare_neg [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) {a : F} (ha : a ≠ 0) : IsSquare a ∨ IsSquare (-a) := by
  rcases FiniteField.pow_dichotomy h2 ha with h | h
  · exact Or.inl ((FiniteField.isSquare_iff h2 ha).mpr h)
  · refine Or.inr ((FiniteField.isSquare_iff h2 (neg_ne_zero.mpr ha)).mpr ?_)
    have hodd : Odd (Fintype.card F / 2) := Nat.odd_iff.mpr (by omega)
    rw [neg_pow, hodd.neg_one_pow, h]
    ring

/-- **A parametrisation of the Paley set.**  In characteristic three, `(u - u⁻¹)²` and its
successor `(u + u⁻¹)²` are both squares, and both are nonzero as soon as `u² ≠ 1` and `-1` is not
a square. -/
theorem sub_inv_sq_mem_paleySet (h30 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F)) {u : Fˣ}
    (hu : u ^ 2 ≠ 1) : ((u : F) - (u : F)⁻¹) ^ 2 ∈ paleySet F := by
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hinv : (u : F) * (u : F)⁻¹ = 1 := mul_inv_cancel₀ hu0
  have hsucc : ((u : F) - (u : F)⁻¹) ^ 2 + 1 = ((u : F) + (u : F)⁻¹) ^ 2 := by
    linear_combination (-4 : F) * hinv - h30
  refine ⟨?_, ⟨_, pow_two _⟩, ?_, ?_⟩
  · -- `u - u⁻¹ = 0` would give `u² = 1`
    intro hzero
    refine hu (Units.ext ?_)
    have hstep : (u : F) - (u : F)⁻¹ = 0 := by
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    have hone : (u : F) * (u : F) = 1 := by linear_combination (u : F) * hstep + hinv
    push_cast
    linear_combination hone
  · -- `u + u⁻¹ = 0` would make `-1` a square
    rw [hsucc]
    intro hzero
    refine hnegsq ⟨(u : F), ?_⟩
    have hsum : (u : F) + (u : F)⁻¹ = 0 := by
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    linear_combination -(u : F) * hsum + hinv
  · exact hsucc ▸ ⟨_, pow_two _⟩

/-- The fibres of the parametrisation `u ↦ (u - u⁻¹)²` have at most four points: `u - u⁻¹`
determines `u` up to inversion, and squaring adds a sign. -/
theorem eq_or_of_sub_inv_sq_eq {u w : Fˣ}
    (h : ((u : F) - (u : F)⁻¹) ^ 2 = ((w : F) - (w : F)⁻¹) ^ 2) :
    u = w ∨ u = -w ∨ u = w⁻¹ ∨ u = -w⁻¹ := by
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hw0 : (w : F) ≠ 0 := w.ne_zero
  -- clear denominators: `((u² - 1) w)² = ((w² - 1) u)²`
  have e1 : ((u : F) - (u : F)⁻¹) * (u : F) = (u : F) ^ 2 - 1 := by field_simp
  have e2 : ((w : F) - (w : F)⁻¹) * (w : F) = (w : F) ^ 2 - 1 := by field_simp
  have hpoly : (((u : F) ^ 2 - 1) * (w : F)) ^ 2 = (((w : F) ^ 2 - 1) * (u : F)) ^ 2 := by
    calc (((u : F) ^ 2 - 1) * (w : F)) ^ 2
        = (((u : F) - (u : F)⁻¹) * ((u : F) * (w : F))) ^ 2 := by rw [← e1]; ring
      _ = (((w : F) - (w : F)⁻¹) * ((u : F) * (w : F))) ^ 2 := by rw [mul_pow, mul_pow, h]; ring
      _ = (((w : F) ^ 2 - 1) * (u : F)) ^ 2 := by rw [← e2]; ring
  -- `((u - w)(uw + 1)) · ((u + w)(uw - 1)) = 0`
  have hfac : (((u : F) - (w : F)) * ((u : F) * (w : F) + 1)) *
      (((u : F) + (w : F)) * ((u : F) * (w : F) - 1)) = 0 := by linear_combination hpoly
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (Units.ext (by linear_combination h2))
    · -- `u w = -1`, i.e. `u = -w⁻¹`
      refine Or.inr (Or.inr (Or.inr (Units.ext ?_)))
      have huw : (u : F) * (w : F) = -1 := by linear_combination h2
      simp only [Units.val_neg, Units.val_inv_eq_inv_val]
      calc (u : F) = (u : F) * (w : F) * (w : F)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hw0, mul_one]
        _ = -(w : F)⁻¹ := by rw [huw]; ring
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · refine Or.inr (Or.inl (Units.ext ?_))
      push_cast
      linear_combination h2
    · -- `u w = 1`, i.e. `u = w⁻¹`
      refine Or.inr (Or.inr (Or.inl (Units.ext ?_)))
      have huw : (u : F) * (w : F) = 1 := by linear_combination h2
      simp only [Units.val_inv_eq_inv_val]
      calc (u : F) = (u : F) * (w : F) * (w : F)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hw0, mul_one]
        _ = (w : F)⁻¹ := by rw [huw, one_mul]

/-- **The Paley set is large**: `|F| - 3 ≤ 4 |T|`.  (In fact `|T| = (|F| - 3)/4`, but only the
lower bound is used.) -/
theorem card_paleySet_lower [Fintype F] (h30 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F))
    (T : Finset F) (hT : ∀ a, a ∈ T ↔ a ∈ paleySet F) : Fintype.card F - 3 ≤ 4 * #T := by
  classical
  have hchar2 : (2 : F) ≠ 0 := fun h2 => hnegsq ⟨1, by linear_combination -h2⟩
  set g : Fˣ → F := fun u => ((u : F) - (u : F)⁻¹) ^ 2 with hg
  set D : Finset Fˣ := {u ∈ univ | u ^ 2 ≠ 1} with hD
  -- the units with `u² = 1` are `±1`, so the domain has `|F| - 3` elements
  have hsq1 : ∀ u : Fˣ, u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
    intro u
    constructor
    · intro hu
      have hval : (u : F) ^ 2 = 1 := by
        have := congrArg (Units.val (α := F)) hu
        simpa using this
      have hfac : ((u : F) - 1) * ((u : F) + 1) = 0 := by linear_combination hval
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact Or.inl (Units.ext (by push_cast; linear_combination h1))
      · exact Or.inr (Units.ext (by push_cast; linear_combination h1))
    · rintro (rfl | rfl) <;> simp
  have hne11 : (1 : Fˣ) ≠ -1 := by
    intro h
    refine hchar2 ?_
    have := congrArg (Units.val (α := F)) h
    push_cast at this
    linear_combination this
  have hDcard : #D = Fintype.card F - 3 := by
    have hsplit : #{u ∈ (univ : Finset Fˣ) | u ^ 2 ≠ 1} + #{u ∈ (univ : Finset Fˣ) | ¬ u ^ 2 ≠ 1}
        = #(univ : Finset Fˣ) :=
      Finset.card_filter_add_card_filter_not (s := (univ : Finset Fˣ)) _
    have hneg : #{u ∈ (univ : Finset Fˣ) | ¬ u ^ 2 ≠ 1} = 2 := by
      have hset : {u ∈ (univ : Finset Fˣ) | ¬ u ^ 2 ≠ 1} = ({1, -1} : Finset Fˣ) := by
        ext u
        simp [hsq1 u]
      rw [hset, Finset.card_insert_of_notMem (by simpa using hne11), Finset.card_singleton]
    have hunits : Fintype.card Fˣ = Fintype.card F - 1 := Fintype.card_units F
    have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Finset.card_univ] at hsplit
    rw [hD]
    omega
  -- the image lands in `T`, with fibres of size at most four
  have himage : D.image g ⊆ T := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    have hu2 : u ^ 2 ≠ 1 := by simpa [hD] using hu
    exact (hT _).mpr (sub_inv_sq_mem_paleySet h30 hnegsq hu2)
  have hfibre : ∀ b ∈ D.image g, #{u ∈ D | g u = b} ≤ 4 := by
    intro b hb
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hb
    refine le_trans (Finset.card_le_card (t := ({w, -w, w⁻¹, -w⁻¹} : Finset Fˣ)) ?_) ?_
    · intro u hu
      have := eq_or_of_sub_inv_sq_eq (F := F) (Finset.mem_filter.mp hu).2
      simpa using this
    · refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
      exact le_trans (Finset.card_insert_le _ _) (by simp)
  calc Fintype.card F - 3 = #D := hDcard.symm
    _ ≤ 4 * #(D.image g) := Finset.card_le_mul_card_image _ _ hfibre
    _ ≤ 4 * #T := Nat.mul_le_mul_left _ (Finset.card_le_card himage)

/-- **Lemma B of BG Appendix C, Problem 1.**  In a finite field of characteristic three with
`|F| ≡ 3 (mod 4)` and `|F| > 9` — e.g. `𝔽_{3^q}` for an odd prime `q` — the Paley set
`T = {a : a and a + 1 are nonzero squares}` generates the additive group.

The proof is the counting argument of the module docstring: `T` is disjoint from `-T` (because
`-1` is not a square), so the subgroup it generates has at least `2|T| ≥ (|F| - 3)/2` elements —
more than the `|F|/3` available in a proper subgroup. -/
theorem addClosure_paleySet_eq_top [Fintype F] (h3 : ringChar F = 3)
    (h4 : Fintype.card F % 4 = 3) (h9 : 9 < Fintype.card F) :
    AddSubgroup.closure (paleySet F) = ⊤ := by
  classical
  haveI : CharP F 3 := ringChar.of_eq h3
  have h30 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    exact_mod_cast this
  have hchar2 : ringChar F ≠ 2 := by rw [h3]; norm_num
  have hnegsq : ¬ IsSquare (-1 : F) := not_isSquare_neg_one hchar2 h4
  set A : AddSubgroup F := AddSubgroup.closure (paleySet F) with hA
  set T : Finset F := {a ∈ univ | a ∈ paleySet F} with hT
  have hTmem : ∀ a, a ∈ T ↔ a ∈ paleySet F := by intro a; simp [hT]
  -- `T` and `-T` are disjoint, and both lie in `A`
  have hdisj : Disjoint T (T.image (fun a => -a)) := by
    refine Finset.disjoint_left.mpr ?_
    intro a haT haneg
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp haneg
    obtain ⟨ha0, hasq, -, -⟩ := (hTmem a).mp haT
    obtain ⟨-, hbsq, -, -⟩ := (hTmem b).mp hb
    have hb' : b = -a := by linear_combination -hba
    refine hnegsq ?_
    have hneg : (-1 : F) = b * a⁻¹ := by rw [hb', neg_mul, mul_inv_cancel₀ ha0]
    rw [hneg]
    exact hbsq.mul hasq.inv
  have hsub : T ∪ T.image (fun a => -a) ⊆ (A : Set F).toFinset := by
    intro a ha
    rw [Set.mem_toFinset]
    rcases Finset.mem_union.mp ha with h | h
    · exact AddSubgroup.subset_closure ((hTmem a).mp h)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact neg_mem (AddSubgroup.subset_closure ((hTmem b).mp hb))
  have hcardA : 2 * #T ≤ Nat.card A := by
    have hcard : #(T ∪ T.image (fun a => -a)) = 2 * #T := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ neg_injective]
      ring
    have hle := Finset.card_le_card hsub
    rw [hcard, Set.toFinset_card, ← Nat.card_eq_fintype_card] at hle
    exact hle
  -- a proper additive subgroup of a field of characteristic three has index at least three
  by_contra hne
  have hmul : Nat.card A * A.index = Nat.card F := AddSubgroup.card_mul_index A
  have hindex : 3 ≤ A.index := by
    have hne1 : A.index ≠ 1 := fun h => hne (AddSubgroup.index_eq_one.mp h)
    obtain ⟨n, -, hn⟩ := FiniteField.card F 3
    have hdvd : A.index ∣ 3 ^ (n : ℕ) :=
      ⟨Nat.card A, by rw [← hn, ← Nat.card_eq_fintype_card, ← hmul]; ring⟩
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (Nat.Prime.dvd_of_dvd_pow hr (hrdvd.trans hdvd))
    have hpos : 0 < A.index := Nat.pos_of_ne_zero fun h0 => by
      have hcardF : 0 < Nat.card F := Nat.card_pos
      rw [h0, mul_zero] at hmul
      omega
    exact hr3 ▸ Nat.le_of_dvd hpos hrdvd
  have h3A : 3 * Nat.card A ≤ Fintype.card F := by
    calc 3 * Nat.card A ≤ A.index * Nat.card A := Nat.mul_le_mul_right _ hindex
      _ = Nat.card F := by rw [mul_comm]; exact hmul
      _ = Fintype.card F := Nat.card_eq_fintype_card
  have hlower : Fintype.card F - 3 ≤ 4 * #T := card_paleySet_lower h30 hnegsq T hTmem
  omega

/-! ## The automatic collision, and why it misses the Paley set -/

section PowDiff

variable {E : ℕ}

/-- The **discrete derivative of the power map**, `D_E(a) = (a+1)^E - a^E`.

In BG Appendix C, Problem 1 this is `D(p) = p^E - (p-1)^E` written at `a = p - 1`, so that
`a ∈ paleySet F` says exactly that `p` and `p - 1` are both non-zero squares. -/
def powDiff (E : ℕ) (a : F) : F := (a + 1) ^ E - a ^ E

/-- **The free 2-to-1 symmetry.**  For *odd* `E` the involution `a ↦ -a-1` preserves `powDiff`:
it exchanges the two terms up to the sign that `(-x)^E = -x^E` supplies.

So `powDiff E` is never injective, and the graph `{(u, u^E)}` — being symmetric under negation —
is never a Sidon set.  The content of BG Appendix C, Problem 1 is therefore *not* about that
graph but about the Paley set, which the involution avoids (`neg_sub_one_notMem_paleySet`). -/
theorem powDiff_neg_sub_one (hE : Odd E) (a : F) : powDiff E (-a - 1) = powDiff E a := by
  have h1 : (-a - 1 + 1 : F) = -a := by ring
  have h2 : (-a - 1 : F) = -(a + 1) := by ring
  rw [powDiff, powDiff, h1, h2, hE.neg_pow, hE.neg_pow]
  ring

/-- **The involution always leaves the Paley set.**  If `-1` is not a square then `a ∈ T` forces
`-a - 1 ∉ T`, because `(-a-1) + 1 = -a` is a non-square.

Hence the automatic collision `powDiff E (-a-1) = powDiff E a` never gives *two* Paley points:
any usable collision is an extra coincidence, which is what makes the general-`q` case of the
criterion an equidistribution question rather than an identity. -/
theorem neg_sub_one_notMem_paleySet (hneg : ¬ IsSquare (-1 : F)) {a : F}
    (ha : a ∈ paleySet F) : -a - 1 ∉ paleySet F := by
  obtain ⟨ha0, hasq, -, -⟩ := ha
  rintro ⟨-, -, -, hsq⟩
  have h1 : (-a - 1 + 1 : F) = -a := by ring
  rw [h1] at hsq
  obtain ⟨r, hr⟩ := hsq
  obtain ⟨t, ht⟩ := hasq
  refine hneg ⟨r * t⁻¹, ?_⟩
  have hstep : (r * t⁻¹) * (r * t⁻¹) = (r * r) * (t * t)⁻¹ := by
    rw [mul_inv]; ring
  rw [hstep, ← hr, ← ht, neg_mul, mul_inv_cancel₀ ha0]

/-! ### Conjugating the `E` and the `E²` collision problem

The exhaustive enumeration for `q = 13` recorded in
`notes/bg/appC_problem1_partial_resolution.md` found that the two exotic exponents `E` and `E²`
give *identical* fibre-size distributions of `powDiff` on the Paley set — all four numbers agree.
That is no accident.  Once `z ↦ z ^ E` has order three, i.e. `z ^ (E * E * E) = z`, the two
problems are conjugate by an explicit map: rescale the `E`-th power by the collision value.

Write `w = powDiff E a` (never zero, `powDiff_ne_zero`).  Both

`powDiffConj E a = a ^ E * w⁻¹`   and   `powDiffConjNeg E a = -(a + 1) ^ E * w⁻¹`

satisfy `powDiff (E * E) · = (w⁻¹) ^ (E * E)`, a value depending on `a` only through `w`.  So each
maps a *fibre* of `powDiff E` into a single fibre of `powDiff (E * E)`, injectively.  Exactly one
of the two lands back inside the Paley set — the first when `w` is a square, the second when it is
not — whence a Paley collision for `E` yields one for `E²`
(`exists_paley_collision_pow_mul`).

Consequence for BG Appendix C, Problem 1: hypothesis (B1) of the trace criterion
`OddOrder.BG.AppC.Problem1.false_of_collisionPair_trace_ne_zero` need only be established for one
exponent out of each conjugate pair `{E, E²}`. -/

section Conjugation

/-- The order-three hypothesis, in the form used below: `z ↦ z ^ E` is a bijection whose square
is its inverse.  For `F = 𝔽_{3^q}` this says `E³ ≡ 1 (mod 3^q - 1)`. -/
theorem pow_pow_mul_self (hcube : ∀ z : F, z ^ (E * E * E) = z) (z : F) :
    (z ^ E) ^ (E * E) = z := by
  rw [← pow_mul, ← mul_assoc]
  exact hcube z

/-- Under the order-three hypothesis `z ↦ z ^ E` is injective. -/
theorem pow_injective_of_cube (hcube : ∀ z : F, z ^ (E * E * E) = z) {x y : F}
    (h : x ^ E = y ^ E) : x = y := by
  have := congrArg (· ^ (E * E)) h
  simpa only [pow_pow_mul_self hcube] using this

/-- **The discrete derivative never vanishes** when `z ↦ z ^ E` is injective: `powDiff E a = 0`
would force `a + 1 = a`. -/
theorem powDiff_ne_zero (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) : powDiff E a ≠ 0 := by
  intro h
  have hpow : (a + 1) ^ E = a ^ E := by
    have := sub_eq_zero.mp h
    exact this
  have := pow_injective_of_cube hcube hpow
  exact one_ne_zero (by linear_combination this)

/-- The conjugating map on the branch where the collision value is a square. -/
def powDiffConj (E : ℕ) (a : F) : F := a ^ E * (powDiff E a)⁻¹

/-- The conjugating map on the branch where the collision value is a non-square. -/
def powDiffConjNeg (E : ℕ) (a : F) : F := -(a + 1) ^ E * (powDiff E a)⁻¹

theorem powDiffConj_add_one (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiffConj E a + 1 = (a + 1) ^ E * (powDiff E a)⁻¹ := by
  have hw : powDiff E a ≠ 0 := powDiff_ne_zero hcube a
  rw [powDiffConj]
  field_simp
  rw [powDiff]
  ring

theorem powDiffConjNeg_add_one (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiffConjNeg E a + 1 = -a ^ E * (powDiff E a)⁻¹ := by
  have hw : powDiff E a ≠ 0 := powDiff_ne_zero hcube a
  rw [powDiffConjNeg]
  field_simp
  rw [powDiff]
  ring

/-- Raising an `E`-th power (times anything) to the `E²` undoes the `E`. -/
private theorem pow_mul_pow_mul_self (hcube : ∀ z : F, z ^ (E * E * E) = z) (x w : F) :
    (x ^ E * w) ^ (E * E) = x * w ^ (E * E) := by
  rw [mul_pow, pow_pow_mul_self hcube]

/-- **The conjugation identity, square branch.**  The image lies in the fibre of `powDiff (E * E)`
over `(powDiff E a)⁻¹ ^ (E * E)`, which depends on `a` only through the collision value. -/
theorem powDiff_powDiffConj (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiff (E * E) (powDiffConj E a) = (powDiff E a)⁻¹ ^ (E * E) := by
  rw [powDiff, powDiffConj_add_one hcube, powDiffConj, pow_mul_pow_mul_self hcube,
    pow_mul_pow_mul_self hcube]
  ring

/-- **The conjugation identity, non-square branch** — the same value as the square branch. -/
theorem powDiff_powDiffConjNeg (hE : Odd E) (hcube : ∀ z : F, z ^ (E * E * E) = z) (a : F) :
    powDiff (E * E) (powDiffConjNeg E a) = (powDiff E a)⁻¹ ^ (E * E) := by
  have hodd : Odd (E * E) := hE.mul hE
  have hneg : ∀ x : F, (-x ^ E * (powDiff E a)⁻¹) ^ (E * E)
      = -(x * (powDiff E a)⁻¹ ^ (E * E)) := by
    intro x
    rw [neg_mul, hodd.neg_pow, pow_mul_pow_mul_self hcube]
  rw [powDiff, powDiffConjNeg_add_one hcube, powDiffConjNeg, hneg a, hneg (a + 1)]
  ring

/-- Squares are closed under the operations used by the two branches. -/
private theorem isSquare_pow_mul_inv {x y : F} (hx : IsSquare x) (hy : IsSquare y) (n : ℕ) :
    IsSquare (x ^ n * y⁻¹) := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hy
  refine ⟨s ^ n * t⁻¹, ?_⟩
  rw [hs, ht, mul_pow, mul_inv]
  ring

/-- **Square branch: the image is again a Paley point.** -/
theorem powDiffConj_mem_paleySet (hcube : ∀ z : F, z ^ (E * E * E) = z) {a : F}
    (ha : a ∈ paleySet F) (hsq : IsSquare (powDiff E a)) : powDiffConj E a ∈ paleySet F := by
  obtain ⟨ha0, hasq, ha1, ha1sq⟩ := ha
  have hw : powDiff E a ≠ 0 := powDiff_ne_zero hcube a
  refine ⟨?_, isSquare_pow_mul_inv hasq hsq E, ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ ha0) (inv_ne_zero hw)
  · rw [powDiffConj_add_one hcube]
    exact mul_ne_zero (pow_ne_zero _ ha1) (inv_ne_zero hw)
  · rw [powDiffConj_add_one hcube]
    exact isSquare_pow_mul_inv ha1sq hsq E

/-- **Non-square branch: the image is again a Paley point.**  Here `-w` is the square, and the
sign in `powDiffConjNeg` is exactly what turns `w⁻¹` into `(-w)⁻¹`. -/
theorem powDiffConjNeg_mem_paleySet [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3)
    (hcube : ∀ z : F, z ^ (E * E * E) = z) {a : F} (ha : a ∈ paleySet F)
    (hsq : ¬ IsSquare (powDiff E a)) : powDiffConjNeg E a ∈ paleySet F := by
  obtain ⟨ha0, hasq, ha1, ha1sq⟩ := ha
  have hw : powDiff E a ≠ 0 := powDiff_ne_zero hcube a
  have hnegsq : IsSquare (-powDiff E a) :=
    (isSquare_or_isSquare_neg h2 h4 hw).resolve_left hsq
  have hinv : ∀ x : F, x * (powDiff E a)⁻¹ = -(x * (-powDiff E a)⁻¹) := by
    intro x
    rw [← neg_inv]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [powDiffConjNeg]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ha1)) (inv_ne_zero hw)
  · have : powDiffConjNeg E a = (a + 1) ^ E * (-powDiff E a)⁻¹ := by
      rw [powDiffConjNeg, neg_mul, hinv ((a + 1) ^ E), neg_neg]
    rw [this]
    exact isSquare_pow_mul_inv ha1sq hnegsq E
  · rw [powDiffConjNeg_add_one hcube]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ ha0)) (inv_ne_zero hw)
  · have : powDiffConjNeg E a + 1 = a ^ E * (-powDiff E a)⁻¹ := by
      rw [powDiffConjNeg_add_one hcube, neg_mul, hinv (a ^ E), neg_neg]
    rw [this]
    exact isSquare_pow_mul_inv hasq hnegsq E

/-- **Conjugation of the two collision problems.**  A collision of `powDiff E` inside the Paley
set produces one of `powDiff (E * E)` inside the Paley set.

Applying it to `E` and to `E²` in turn (both are odd and both satisfy the order-three hypothesis)
shows the two problems are equivalent, which is why the measured fibre-size distributions agree
exactly.  For BG Appendix C, Problem 1 this halves the work: hypothesis (B1) has to be proved for
only one exponent of each pair `{E, E²}`. -/
theorem exists_paley_collision_pow_mul [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3)
    (hE : Odd E) (hcube : ∀ z : F, z ^ (E * E * E) = z) {a b : F} (ha : a ∈ paleySet F)
    (hb : b ∈ paleySet F) (hab : a ≠ b) (hval : powDiff E a = powDiff E b) :
    ∃ c ∈ paleySet F, ∃ d ∈ paleySet F, c ≠ d ∧ powDiff (E * E) c = powDiff (E * E) d := by
  have hw : powDiff E a ≠ 0 := powDiff_ne_zero hcube a
  have hwinv : (powDiff E a)⁻¹ ≠ 0 := inv_ne_zero hw
  by_cases hsq : IsSquare (powDiff E a)
  · refine ⟨powDiffConj E a, powDiffConj_mem_paleySet hcube ha hsq, powDiffConj E b,
      powDiffConj_mem_paleySet hcube hb (hval ▸ hsq), ?_, ?_⟩
    · simp only [powDiffConj, ← hval]
      intro h
      exact hab (pow_injective_of_cube hcube (mul_right_cancel₀ hwinv h))
    · rw [powDiff_powDiffConj hcube, powDiff_powDiffConj hcube, hval]
  · refine ⟨powDiffConjNeg E a, powDiffConjNeg_mem_paleySet h2 h4 hcube ha hsq,
      powDiffConjNeg E b, powDiffConjNeg_mem_paleySet h2 h4 hcube hb (hval ▸ hsq), ?_, ?_⟩
    · simp only [powDiffConjNeg, ← hval]
      intro h
      have h' : (a + 1) ^ E = (b + 1) ^ E := by
        have := mul_right_cancel₀ hwinv h
        linear_combination -this
      have := pow_injective_of_cube hcube h'
      exact hab (by linear_combination this)
    · rw [powDiff_powDiffConjNeg hE hcube, powDiff_powDiffConjNeg hE hcube, hval]

end Conjugation

/-! ### Collisions supplied by the fixed subgroup of `z ↦ z ^ E`

The map `omega : z ↦ z ^ E` has a fixed subgroup `Fix = {z : z ^ E = z}` (of order
`gcd(E - 1, |F| - 1)` inside `Fˣ`).  It forces collision values, and hence collisions, with no
search at all.

The mechanism: if `a` and `a + 1` lie in the *same* coset of `Fix`, say `a ^ E = c ⬝ a` and
`(a + 1) ^ E = c ⬝ (a + 1)` for a common `c`, then

`powDiff E a = c ⬝ (a + 1) - c ⬝ a = c`,

a value that depends only on the coset (`powDiff_eq_of_pow_eq_mul`).  Two Paley points in the same
coset therefore collide.

Such points are parametrised by `Fix` itself through the Möbius map `t ↦ t / (1 - t)`: for
`a = t / (1 - t)` one has `a + 1 = (1 - t)⁻¹` and `a = t ⬝ (a + 1)`, so `a` and `a + 1` lie in the
same coset precisely when `t ∈ Fix`, and then the collision value is `(1 - t) / (1 - t) ^ E`
(`mem_paleySet_powDiff_of_pow_eq`).  Two fixed nonzero squares `t ≠ t'` with equal values give a
collision outright (`exists_paley_collision_of_pow_eq`).

This is the "structured exponent" certificate of
`notes/bg/appC_problem1_partial_resolution.md`, in a form strictly stronger than the one recorded
there.  That version is the special case `c = 1`, which additionally demands `1 - t ∈ Fix`
(`exists_paley_collision_of_pow_eq_of_sub`); it bites only when `|Fix| > √|F|`, since the expected
number of usable `t` is `|Fix|² / |F|`.  The general version only needs two of the `|Fix|` values
`(1 - t) / (1 - t) ^ E` to coincide, and those lie in a set of size `(|F| - 1) / |Fix|`, so a
birthday collision is expected once `|Fix|³ ≳ |F|` — the threshold drops from `|F|^{1/2}` to
`|F|^{1/3}`, and the search cost from `√(|F| / q)` field operations to `√((|F| - 1) / |Fix|)`.

Nothing in this subsection uses characteristic three, or finiteness. -/

section FixedSubgroup

/-- **A Paley point whose two coordinates lie in the same coset of the fixed subgroup has that
coset as its collision value.** -/
theorem powDiff_eq_of_pow_eq_mul {a c : F} (ha : a ^ E = c * a) (ha1 : (a + 1) ^ E = c * (a + 1)) :
    powDiff E a = c := by
  rw [powDiff, ha, ha1]
  ring

/-- **The search-free parametrisation.**  If `t` is a nonzero square fixed by `z ↦ z ^ E` and
`1 - t` is a nonzero square, then `a = t / (1 - t)` is a Paley point, and its collision value
`(1 - t) / (1 - t) ^ E` is computable from `t` alone.

No hypothesis is placed on `1 - t` beyond being a square: `t ∈ Fix` alone already puts `a` and
`a + 1` into a common coset of `Fix`. -/
theorem pow_eq_mul_of_pow_eq {t : F} (ht1 : t ≠ 1) (hft : t ^ E = t) :
    (t / (1 - t)) ^ E = ((1 - t) / (1 - t) ^ E) * (t / (1 - t)) ∧
      (t / (1 - t) + 1) ^ E = ((1 - t) / (1 - t) ^ E) * (t / (1 - t) + 1) := by
  have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hdE : ((1 : F) - t) ^ E ≠ 0 := pow_ne_zero _ hd
  have hsucc : t / (1 - t) + 1 = (1 - t)⁻¹ := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [div_pow, hft]
    field_simp
  · rw [hsucc, inv_pow]
    field_simp

theorem mem_paleySet_powDiff_of_pow_eq {t : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hft : t ^ E = t) (hst : IsSquare t) (hs1 : IsSquare (1 - t)) :
    t / (1 - t) ∈ paleySet F ∧ powDiff E (t / (1 - t)) = (1 - t) / (1 - t) ^ E := by
  have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hsucc : t / (1 - t) + 1 = (1 - t)⁻¹ := by
    field_simp
    ring
  have hinvsq : IsSquare ((1 - t)⁻¹) := by
    obtain ⟨u, hu⟩ := hs1
    exact ⟨u⁻¹, by rw [hu, mul_inv]⟩
  have hasq : IsSquare (t / (1 - t)) := by
    obtain ⟨s, hs⟩ := hst
    obtain ⟨u, hu⟩ := hinvsq
    refine ⟨s * u, ?_⟩
    rw [div_eq_mul_inv, hu, hs]
    ring
  obtain ⟨hsc, hsc1⟩ := pow_eq_mul_of_pow_eq ht1 hft
  exact ⟨⟨div_ne_zero ht0 hd, hasq, by rw [hsucc]; exact inv_ne_zero hd,
    by rw [hsucc]; exact hinvsq⟩, powDiff_eq_of_pow_eq_mul hsc hsc1⟩

/-- **Two fixed squares with the same collision value give a Paley collision**, hence hypothesis
(B1) for this exponent.  The Möbius map `t ↦ t / (1 - t)` is injective, so distinct `t` give
distinct Paley points. -/
theorem exists_paley_collision_of_pow_eq {t t' : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hft : t ^ E = t) (hst : IsSquare t) (hs1 : IsSquare (1 - t))
    (ht0' : t' ≠ 0) (ht1' : t' ≠ 1) (hft' : t' ^ E = t')
    (hst' : IsSquare t') (hs1' : IsSquare (1 - t'))
    (hval : (1 - t) / (1 - t) ^ E = (1 - t') / (1 - t') ^ E) (hne : t ≠ t') :
    ∃ a ∈ paleySet F, ∃ b ∈ paleySet F, a ≠ b ∧ powDiff E a = powDiff E b := by
  obtain ⟨hmem, hv⟩ := mem_paleySet_powDiff_of_pow_eq ht0 ht1 hft hst hs1
  obtain ⟨hmem', hv'⟩ := mem_paleySet_powDiff_of_pow_eq ht0' ht1' hft' hst' hs1'
  have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hd' : (1 : F) - t' ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1')
  refine ⟨_, hmem, _, hmem', ?_, by rw [hv, hv', hval]⟩
  intro hcontra
  refine hne ?_
  field_simp at hcontra
  linear_combination hcontra

/-- The special case where `1 - t` is fixed as well: both collision values are then `1`, so the
matching hypothesis of `exists_paley_collision_of_pow_eq` is automatic.  This is the form of the
certificate recorded in `notes/bg/appC_problem1_partial_resolution.md`. -/
theorem exists_paley_collision_of_pow_eq_of_sub {t t' : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hft : t ^ E = t) (hf1 : (1 - t) ^ E = 1 - t) (hst : IsSquare t) (hs1 : IsSquare (1 - t))
    (ht0' : t' ≠ 0) (ht1' : t' ≠ 1) (hft' : t' ^ E = t') (hf1' : (1 - t') ^ E = 1 - t')
    (hst' : IsSquare t') (hs1' : IsSquare (1 - t')) (hne : t ≠ t') :
    ∃ a ∈ paleySet F, ∃ b ∈ paleySet F, a ≠ b ∧ powDiff E a = powDiff E b := by
  have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hd' : (1 : F) - t' ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1')
  refine exists_paley_collision_of_pow_eq ht0 ht1 hft hst hs1 ht0' ht1' hft' hst' hs1' ?_ hne
  rw [hf1, hf1', div_self hd, div_self hd']

/-! ### Counting the fixed-point parameters

The parameters `t` come in inversion pairs `{t, t⁻¹}`, and the two members are never both usable:
`1 - t⁻¹ = -(1 - t) · t⁻¹` differs from `1 - t` by the non-square `-1`.  So exactly *half* of the
fixed nonzero squares `t ≠ 1` give a Paley point, which is the counting input of the gcd criterion
of `notes/bg/appC_problem1_chatgpt_answer_b1.md` (Theorem A there). -/

/-- If `x` and `-x` are both squares then so is `-1`. -/
theorem isSquare_neg_one_of_isSquare_neg {x : F} (hx : x ≠ 0) (h1 : IsSquare x)
    (h2 : IsSquare (-x)) : IsSquare (-1 : F) := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨u, hu⟩ := h2
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hs)
  refine ⟨u * s⁻¹, ?_⟩
  have hstep : (u * s⁻¹) * (u * s⁻¹) = (u * u) * (s * s)⁻¹ := by
    rw [mul_inv]
    ring
  rw [hstep, ← hu, ← hs, neg_mul, mul_inv_cancel₀ hx]

/-- **The inversion pairing.**  For a nonzero square `t ≠ 1`, exactly one of `t` and `t⁻¹` is a
usable parameter: `1 - t⁻¹` is a square precisely when `1 - t` is not. -/
theorem isSquare_one_sub_inv_iff [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) {t : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hst : IsSquare t) :
    IsSquare (1 - t⁻¹) ↔ ¬ IsSquare (1 - t) := by
  have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hinvsq : IsSquare t⁻¹ := by
    obtain ⟨s, hs⟩ := hst
    exact ⟨s⁻¹, by rw [hs, mul_inv]⟩
  have hrw : (1 : F) - t⁻¹ = -((1 - t) * t⁻¹) := by
    field_simp
    ring
  constructor
  · rintro hsq hcon
    refine not_isSquare_neg_one h2 h4 ?_
    refine isSquare_neg_one_of_isSquare_neg (x := (1 - t) * t⁻¹)
      (mul_ne_zero hd (inv_ne_zero ht0)) ?_ ?_
    · obtain ⟨s, hs⟩ := hcon
      obtain ⟨u, hu⟩ := hinvsq
      exact ⟨s * u, by rw [hs, hu]; ring⟩
    · rwa [← hrw]
  · intro hcon
    have hnegsq : IsSquare (-(1 - t)) := (isSquare_or_isSquare_neg h2 h4 hd).resolve_left hcon
    obtain ⟨s, hs⟩ := hnegsq
    obtain ⟨u, hu⟩ := hinvsq
    refine ⟨s * u, ?_⟩
    rw [hrw, ← neg_mul, hs, hu]
    ring

/-- **Exactly half of the parameters are usable.**  Inversion pairs off `L ∖ {1}` — its only
fixed points would be `±1`, and `-1` is not a square, so it is not in `L` — and by
`isSquare_one_sub_inv_iff` exactly one member of each pair has `1 - ·` a square.

Here `L` is the fixed subgroup inside the squares, `Pos` its usable half and `Neg` the other. -/
theorem two_mul_card_usable_add_one [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) (L Pos Neg : Finset F)
    (hL : ∀ t, t ∈ L ↔ (t ≠ 0 ∧ IsSquare t ∧ t ^ E = t))
    (hPos : ∀ t, t ∈ Pos ↔ (t ∈ L ∧ t ≠ 1 ∧ IsSquare (1 - t)))
    (hNeg : ∀ t, t ∈ Neg ↔ (t ∈ L ∧ t ≠ 1 ∧ ¬ IsSquare (1 - t))) :
    2 * Pos.card + 1 = L.card := by
  classical
  -- `L` is closed under inversion
  have hLinv : ∀ t ∈ L, t⁻¹ ∈ L := by
    intro t ht
    obtain ⟨ht0, htsq, htf⟩ := (hL t).mp ht
    refine (hL _).mpr ⟨inv_ne_zero ht0, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := htsq
      exact ⟨s⁻¹, by rw [hs, mul_inv]⟩
    · rw [inv_pow, htf]
  -- inversion is a bijection between the two halves
  have hcard : Pos.card = Neg.card := by
    refine Finset.card_bij' (fun t _ => t⁻¹) (fun t _ => t⁻¹) ?_ ?_ ?_ ?_
    · intro t ht
      obtain ⟨htL, ht1, htsq⟩ := (hPos t).mp ht
      obtain ⟨ht0, htsq', -⟩ := (hL t).mp htL
      refine (hNeg _).mpr ⟨hLinv t htL, ?_, ?_⟩
      · intro hcon
        exact ht1 (by simpa using congrArg (·⁻¹) hcon)
      · rw [isSquare_one_sub_inv_iff h2 h4 ht0 ht1 htsq']
        exact not_not.mpr htsq
    · intro t ht
      obtain ⟨htL, ht1, htsq⟩ := (hNeg t).mp ht
      obtain ⟨ht0, htsq', -⟩ := (hL t).mp htL
      refine (hPos _).mpr ⟨hLinv t htL, ?_, ?_⟩
      · intro hcon
        exact ht1 (by simpa using congrArg (·⁻¹) hcon)
      · by_contra hcon
        rw [← isSquare_one_sub_inv_iff h2 h4 (inv_ne_zero ht0) ?_ ?_] at hcon
        · rw [inv_inv] at hcon
          exact htsq hcon
        · intro hc
          exact ht1 (by simpa using congrArg (·⁻¹) hc)
        · obtain ⟨s, hs⟩ := htsq'
          exact ⟨s⁻¹, by rw [hs, mul_inv]⟩
    · intro t _
      exact inv_inv t
    · intro t _
      exact inv_inv t
  -- `L` is the disjoint union of `{1}`, `Pos` and `Neg`
  have hone : (1 : F) ∈ L := (hL 1).mpr ⟨one_ne_zero, ⟨1, (one_mul 1).symm⟩, one_pow E⟩
  have hdisj : Disjoint Pos Neg := by
    refine Finset.disjoint_left.mpr ?_
    intro t htp htn
    exact ((hNeg t).mp htn).2.2 ((hPos t).mp htp).2.2
  have hsplit : L = insert 1 (Pos ∪ Neg) := by
    ext t
    simp only [Finset.mem_insert, Finset.mem_union, hPos, hNeg]
    constructor
    · intro ht
      by_cases h1 : t = 1
      · exact Or.inl h1
      · by_cases hs : IsSquare (1 - t)
        · exact Or.inr (Or.inl ⟨ht, h1, hs⟩)
        · exact Or.inr (Or.inr ⟨ht, h1, hs⟩)
    · rintro (rfl | ⟨ht, -, -⟩ | ⟨ht, -, -⟩)
      · exact hone
      · exact ht
      · exact ht
  have hnotmem : (1 : F) ∉ Pos ∪ Neg := by
    simp only [Finset.mem_union, hPos, hNeg]
    rintro (⟨-, h, -⟩ | ⟨-, h, -⟩) <;> exact h rfl
  rw [hsplit, Finset.card_insert_of_notMem hnotmem, Finset.card_union_of_disjoint hdisj, ← hcard]
  ring

/-- Two distinct usable parameters with the same value give two Paley points sharing a scaling
factor. -/
theorem exists_sameCoset_pair_of_eq {t t' : F} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hft : t ^ E = t)
    (hst : IsSquare t) (hs1 : IsSquare (1 - t)) (ht0' : t' ≠ 0) (ht1' : t' ≠ 1)
    (hft' : t' ^ E = t') (hst' : IsSquare t') (hs1' : IsSquare (1 - t')) (hne : t ≠ t')
    (hval : (1 - t) / (1 - t) ^ E = (1 - t') / (1 - t') ^ E) :
    ∃ a b lam : F, a ∈ paleySet F ∧ b ∈ paleySet F ∧ a ≠ b ∧
      a ^ E = lam * a ∧ (a + 1) ^ E = lam * (a + 1) ∧
      b ^ E = lam * b ∧ (b + 1) ^ E = lam * (b + 1) := by
  have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hd' : (1 : F) - t' ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1')
  obtain ⟨hmem, -⟩ := mem_paleySet_powDiff_of_pow_eq ht0 ht1 hft hst hs1
  obtain ⟨hmem', -⟩ := mem_paleySet_powDiff_of_pow_eq ht0' ht1' hft' hst' hs1'
  obtain ⟨hsc, hsc1⟩ := pow_eq_mul_of_pow_eq ht1 hft
  obtain ⟨hsc', hsc1'⟩ := pow_eq_mul_of_pow_eq ht1' hft'
  rw [← hval] at hsc' hsc1'
  refine ⟨t / (1 - t), t' / (1 - t'), (1 - t) / (1 - t) ^ E, hmem, hmem', ?_,
    hsc, hsc1, hsc', hsc1'⟩
  intro hcontra
  refine hne ?_
  field_simp at hcontra
  linear_combination hcontra

/-- **Theorem A, pigeonhole form.**  If the usable fixed-point parameters outnumber the collision
values they produce, then two of them give *distinct* Paley points sharing one scaling factor —
that is, two Paley points in a single coset of the fixed subgroup.

This is exactly the input of `OddOrder.BG.AppC.Problem1.false_of_sameCoset_pair`. -/
theorem exists_sameCoset_pair_of_card_lt (P V : Finset F)
    (hP : ∀ t ∈ P, t ≠ 0 ∧ t ≠ 1 ∧ t ^ E = t ∧ IsSquare t ∧ IsSquare (1 - t))
    (hV : ∀ t ∈ P, (1 - t) / (1 - t) ^ E ∈ V) (hcard : V.card < P.card) :
    ∃ a b lam : F, a ∈ paleySet F ∧ b ∈ paleySet F ∧ a ≠ b ∧
      a ^ E = lam * a ∧ (a + 1) ^ E = lam * (a + 1) ∧
      b ^ E = lam * b ∧ (b + 1) ^ E = lam * (b + 1) := by
  obtain ⟨t, htP, t', ht'P, hne, hval⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hV
  obtain ⟨ht0, ht1, hft, hst, hs1⟩ := hP t htP
  obtain ⟨ht0', ht1', hft', hst', hs1'⟩ := hP t' ht'P
  exact exists_sameCoset_pair_of_eq ht0 ht1 hft hst hs1 ht0' ht1' hft' hst' hs1' hne hval

/-- **Fibre counting.**  If a finite set `S` is stable under multiplication by a finite set `L` of
nonzero scalars and `f` is constant on those translates, then each fibre of `f` on `S` has at least
`|L|` elements, so `|f(S)| · |L| ≤ |S|`.

Applied to `S` = the nonzero squares, `f u = u^E · u⁻¹` and `L` = the fixed squares, this is the
index bound `|V| ≤ [U : L]` of the gcd criterion. -/
theorem card_image_mul_card_le [DecidableEq F] (S L : Finset F) (f : F → F)
    (hS0 : ∀ u ∈ S, u ≠ 0) (hmul : ∀ u ∈ S, ∀ l ∈ L, u * l ∈ S)
    (hf : ∀ u ∈ S, ∀ l ∈ L, f (u * l) = f u) :
    (S.image f).card * L.card ≤ S.card := by
  classical
  have hfib : ∀ v ∈ S.image f, L.card ≤ (S.filter fun u => f u = v).card := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    refine Finset.card_le_card_of_injOn (fun l => u * l) ?_ ?_
    · intro l hl
      exact Finset.mem_filter.mpr ⟨hmul u hu l hl, hf u hu l hl⟩
    · intro l₁ _ l₂ _ heq
      exact mul_left_cancel₀ (hS0 u hu) heq
  calc (S.image f).card * L.card
      = ∑ _v ∈ S.image f, L.card := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ v ∈ S.image f, (S.filter fun u => f u = v).card := Finset.sum_le_sum hfib
    _ = S.card :=
        (Finset.card_eq_sum_card_fiberwise fun u hu => Finset.mem_image_of_mem f hu).symm

/-- **The index bound.**  The collision values produced by the fixed subgroup all lie in the image
of `u ↦ u ^ E · u⁻¹` on the nonzero squares, and that image has at most `|U| / |L|` elements. -/
theorem card_values_mul_card_le [DecidableEq F] (Usq L : Finset F)
    (hUsq : ∀ u, u ∈ Usq ↔ (u ≠ 0 ∧ IsSquare u))
    (hL : ∀ t, t ∈ L ↔ (t ≠ 0 ∧ IsSquare t ∧ t ^ E = t)) :
    (Usq.image fun u => u ^ E * u⁻¹).card * L.card ≤ Usq.card := by
  refine card_image_mul_card_le Usq L _ (fun u hu => ((hUsq u).mp hu).1) ?_ ?_
  · intro u hu l hl
    obtain ⟨hu0, hus⟩ := (hUsq u).mp hu
    obtain ⟨hl0, hls, -⟩ := (hL l).mp hl
    refine (hUsq _).mpr ⟨mul_ne_zero hu0 hl0, ?_⟩
    obtain ⟨s, hs⟩ := hus
    obtain ⟨t, ht⟩ := hls
    exact ⟨s * t, by rw [hs, ht]; ring⟩
  · intro u hu l hl
    obtain ⟨hu0, -⟩ := (hUsq u).mp hu
    obtain ⟨hl0, -, hlf⟩ := (hL l).mp hl
    rw [mul_pow, hlf, mul_inv]
    field_simp

/-- **Theorem A, criterion form.**  Once the fixed subgroup `L` is more than twice as large as the
set of collision values it can produce, two Paley points must share a coset — and then
`OddOrder.BG.AppC.Problem1.false_of_sameCoset_pair` refutes hypothesis (B).

With `|V| ≤ [U : L]` this is the gcd criterion `|L| ≥ 2[U : L] + 2`.  (The sharper `|L| ≥
2[U : L] + 1` needs one further parity refinement, namely that the coset of `L` itself carries an
even number of Paley points.) -/
theorem exists_sameCoset_pair_of_card [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) (L Pos Neg V : Finset F)
    (hL : ∀ t, t ∈ L ↔ (t ≠ 0 ∧ IsSquare t ∧ t ^ E = t))
    (hPos : ∀ t, t ∈ Pos ↔ (t ∈ L ∧ t ≠ 1 ∧ IsSquare (1 - t)))
    (hNeg : ∀ t, t ∈ Neg ↔ (t ∈ L ∧ t ≠ 1 ∧ ¬ IsSquare (1 - t)))
    (hV : ∀ t ∈ Pos, (1 - t) / (1 - t) ^ E ∈ V)
    (hcards : 2 * V.card + 1 < L.card) :
    ∃ a b lam : F, a ∈ paleySet F ∧ b ∈ paleySet F ∧ a ≠ b ∧
      a ^ E = lam * a ∧ (a + 1) ^ E = lam * (a + 1) ∧
      b ^ E = lam * b ∧ (b + 1) ^ E = lam * (b + 1) := by
  have hcount := two_mul_card_usable_add_one h2 h4 L Pos Neg hL hPos hNeg
  refine exists_sameCoset_pair_of_card_lt Pos V ?_ hV ?_
  · intro t ht
    obtain ⟨htL, ht1, hsq⟩ := (hPos t).mp ht
    obtain ⟨ht0, htsq, htf⟩ := (hL t).mp htL
    exact ⟨ht0, ht1, htf, htsq, hsq⟩
  · omega

/-- **Theorem A, arithmetic form.**  Writing `a = |L|` for the size of the fixed subgroup inside
the squares and `n = |U|` for the number of nonzero squares, the single inequality

`a (a - 1) > 2 n`

forces two Paley points into one coset, and hence (through
`OddOrder.BG.AppC.Problem1.false_of_sameCoset_pair`) refutes hypothesis (B).

For `F = 𝔽_{3^q}` one has `a = gcd(E - 1, n)` and `n = (3^q - 1)/2`, so this is the gcd criterion
of `notes/bg/appC_problem1_chatgpt_answer_b1.md`, up to the one unit that the parity refinement
there gains. -/
theorem exists_sameCoset_pair_of_card_arith [Fintype F] (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) (Usq L Pos Neg : Finset F)
    (hUsq : ∀ u, u ∈ Usq ↔ (u ≠ 0 ∧ IsSquare u))
    (hL : ∀ t, t ∈ L ↔ (t ≠ 0 ∧ IsSquare t ∧ t ^ E = t))
    (hPos : ∀ t, t ∈ Pos ↔ (t ∈ L ∧ t ≠ 1 ∧ IsSquare (1 - t)))
    (hNeg : ∀ t, t ∈ Neg ↔ (t ∈ L ∧ t ≠ 1 ∧ ¬ IsSquare (1 - t)))
    (harith : 2 * Usq.card + L.card < L.card * L.card) :
    ∃ a b lam : F, a ∈ paleySet F ∧ b ∈ paleySet F ∧ a ≠ b ∧
      a ^ E = lam * a ∧ (a + 1) ^ E = lam * (a + 1) ∧
      b ^ E = lam * b ∧ (b + 1) ^ E = lam * (b + 1) := by
  classical
  set V : Finset F := Usq.image fun u => u ^ E * u⁻¹ with hV
  have hbound : V.card * L.card ≤ Usq.card := card_values_mul_card_le Usq L hUsq hL
  have hmaps : ∀ t ∈ Pos, (1 - t) / (1 - t) ^ E ∈ V := by
    intro t ht
    obtain ⟨htL, ht1, hs1⟩ := (hPos t).mp ht
    obtain ⟨ht0, hst, hft⟩ := (hL t).mp htL
    obtain ⟨hmem, -⟩ := mem_paleySet_powDiff_of_pow_eq ht0 ht1 hft hst hs1
    obtain ⟨ha0, hasq, -, -⟩ := hmem
    obtain ⟨hsc, -⟩ := pow_eq_mul_of_pow_eq ht1 hft
    refine Finset.mem_image.mpr ⟨t / (1 - t), (hUsq _).mpr ⟨ha0, hasq⟩, ?_⟩
    rw [hsc, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
  refine exists_sameCoset_pair_of_card h2 h4 L Pos Neg V hL hPos hNeg hmaps ?_
  have hone : (1 : F) ∈ L := (hL 1).mpr ⟨one_ne_zero, ⟨1, (one_mul 1).symm⟩, one_pow E⟩
  have hL1 : 0 < L.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hprod : (2 * V.card + 1) * L.card < L.card * L.card := by
    have hexp : (2 * V.card + 1) * L.card = 2 * (V.card * L.card) + L.card := by ring
    omega
  exact Nat.lt_of_mul_lt_mul_right hprod

/-- **The trivial coset carries an even number of parameters.**  On the fibre over the value `1`
— the parameters `t` for which `1 - t` is *also* fixed — the involution `t ↦ 1 - t` acts without
fixed points: a fixed point would satisfy `2t = 1`, i.e. `t = -1` in characteristic three, and `-1`
is not a square. -/
theorem two_dvd_card_trivial_fibre [Fintype F] (h3 : (3 : F) = 0) (h2 : ringChar F ≠ 2)
    (h4 : Fintype.card F % 4 = 3) (T0 : Finset F)
    (hT0 : ∀ t, t ∈ T0 ↔ (t ≠ 0 ∧ t ≠ 1 ∧ IsSquare t ∧ IsSquare (1 - t) ∧ t ^ E = t
      ∧ (1 - t) ^ E = 1 - t)) :
    2 ∣ T0.card := by
  classical
  have hnegsq : ¬ IsSquare (-1 : F) := not_isSquare_neg_one h2 h4
  have hmem : ∀ t ∈ T0, (1 : F) - t ∈ T0 := by
    intro t ht
    obtain ⟨ht0, ht1, hst, hs1, hft, hf1⟩ := (hT0 t).mp ht
    have hrw : (1 : F) - (1 - t) = t := by ring
    exact (hT0 _).mpr ⟨sub_ne_zero.mpr (Ne.symm ht1), by
      intro hcon
      exact ht0 (by linear_combination -hcon), hs1, by rw [hrw]; exact hst, hf1, by
      rw [hrw]; exact hft⟩
  have hnofix : ∀ t ∈ T0, (1 : F) - t ≠ t := by
    intro t ht hcon
    obtain ⟨-, -, hst, -, -, -⟩ := (hT0 t).mp ht
    refine hnegsq ?_
    have htval : t = -1 := by linear_combination hcon + t * h3
    rwa [htval] at hst
  have hsum : ∑ _t ∈ T0, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (f := fun _ : F => (1 : ZMod 2)) (fun t _ => 1 - t)
      (fun _ _ => by decide) (fun t ht _ => hnofix t ht) hmem (fun t _ => by ring)
  have hcast : ((T0.card : ℕ) : ZMod 2) = 0 := by simpa using hsum
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- **Theorem A, sharp criterion.**  The parity of the trivial fibre buys one unit: `2 |V| ≤ |L|`
already forces two Paley points into one coset, whereas `exists_sameCoset_pair_of_card` needed the
strict inequality.

If every value were attained at most once, the trivial fibre — of even size — would be empty, so
the values actually attained would avoid `1` and there would be at most `|V| - 1` of them; but
`2|V| ≤ |L| = 2|Pos| + 1` gives `|V| ≤ |Pos|`. -/
theorem exists_sameCoset_pair_of_two_mul_card_le [Fintype F] (h3 : (3 : F) = 0)
    (h2 : ringChar F ≠ 2) (h4 : Fintype.card F % 4 = 3) (L Pos Neg V : Finset F)
    (hL : ∀ t, t ∈ L ↔ (t ≠ 0 ∧ IsSquare t ∧ t ^ E = t))
    (hPos : ∀ t, t ∈ Pos ↔ (t ∈ L ∧ t ≠ 1 ∧ IsSquare (1 - t)))
    (hNeg : ∀ t, t ∈ Neg ↔ (t ∈ L ∧ t ≠ 1 ∧ ¬ IsSquare (1 - t)))
    (hV : ∀ t ∈ Pos, (1 - t) / (1 - t) ^ E ∈ V) (hVone : (1 : F) ∈ V)
    (hcards : 2 * V.card ≤ L.card) :
    ∃ a b lam : F, a ∈ paleySet F ∧ b ∈ paleySet F ∧ a ≠ b ∧
      a ^ E = lam * a ∧ (a + 1) ^ E = lam * (a + 1) ∧
      b ^ E = lam * b ∧ (b + 1) ^ E = lam * (b + 1) := by
  classical
  have hcount := two_mul_card_usable_add_one h2 h4 L Pos Neg hL hPos hNeg
  by_cases hinj : ∀ t ∈ Pos, ∀ t' ∈ Pos, (1 - t) / (1 - t) ^ E = (1 - t') / (1 - t') ^ E → t = t'
  · exfalso
    -- the value `1` is attained exactly on the parameters whose partner is fixed too
    have hval1 : ∀ t ∈ Pos, ((1 - t) / (1 - t) ^ E = 1 ↔ (1 - t) ^ E = 1 - t) := by
      intro t ht
      obtain ⟨-, ht1, -⟩ := (hPos t).mp ht
      have hd : (1 : F) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
      rw [div_eq_one_iff_eq (pow_ne_zero _ hd)]
      exact eq_comm
    set T0 := Pos.filter fun t => (1 - t) ^ E = 1 - t with hT0def
    have hT0 : ∀ t, t ∈ T0 ↔ (t ≠ 0 ∧ t ≠ 1 ∧ IsSquare t ∧ IsSquare (1 - t) ∧ t ^ E = t
        ∧ (1 - t) ^ E = 1 - t) := by
      intro t
      simp only [hT0def, Finset.mem_filter, hPos, hL]
      constructor
      · rintro ⟨⟨⟨h0, hs, hf⟩, h1, hsq⟩, hfix⟩
        exact ⟨h0, h1, hs, hsq, hf, hfix⟩
      · rintro ⟨h0, h1, hs, hsq, hf, hfix⟩
        exact ⟨⟨⟨h0, hs, hf⟩, h1, hsq⟩, hfix⟩
    have hpar := two_dvd_card_trivial_fibre h3 h2 h4 T0 hT0
    have hT0le : T0.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      obtain ⟨hxP, hxf⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyP, hyf⟩ := Finset.mem_filter.mp hy
      exact hinj x hxP y hyP (by rw [(hval1 x hxP).mpr hxf, (hval1 y hyP).mpr hyf])
    have hT0empty : T0 = ∅ := Finset.card_eq_zero.mp (by omega)
    have himg : Pos.image (fun t => (1 - t) / (1 - t) ^ E) ⊆ V.erase 1 := by
      intro v hv
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_erase.mpr ⟨?_, hV t ht⟩
      intro hone
      have : t ∈ T0 := Finset.mem_filter.mpr ⟨ht, (hval1 t ht).mp hone⟩
      rw [hT0empty] at this
      exact absurd this (Finset.notMem_empty t)
    have hcardimg : (Pos.image fun t => (1 - t) / (1 - t) ^ E).card = Pos.card :=
      Finset.card_image_of_injOn fun x hx y hy h => hinj x hx y hy h
    have hle := Finset.card_le_card himg
    rw [hcardimg, Finset.card_erase_of_mem hVone] at hle
    have hV1 : 1 ≤ V.card := Finset.card_pos.mpr ⟨1, hVone⟩
    omega
  · push Not at hinj
    obtain ⟨t, ht, t', ht', hvv, hne⟩ := hinj
    obtain ⟨htL, ht1, hs1⟩ := (hPos t).mp ht
    obtain ⟨ht0, hst, hft⟩ := (hL t).mp htL
    obtain ⟨htL', ht1', hs1'⟩ := (hPos t').mp ht'
    obtain ⟨ht0', hst', hft'⟩ := (hL t').mp htL'
    exact exists_sameCoset_pair_of_eq ht0 ht1 hft hst hs1 ht0' ht1' hft' hst' hs1' hne hvv

/-! ### Collisions forced by the Frobenius, and by additivity at one point

Two mechanisms that need only a **single** Paley point.  Both rest on the same elementary fact:

**the Paley set avoids the prime field** (`notMem_prime_field_of_mem_paleySet`) — `0` and `-1` are
excluded outright and `1` is excluded because `1 + 1 = -1` is a non-square —

while `powDiff` is equivariant for the two maps that *preserve* the Paley set:

* the Frobenius `a ↦ a³`, with `powDiff E (a³) = (powDiff E a)³`;
* the inversion `a ↦ a⁻¹`, whose fixed points `±1` are outside the Paley set.

So a Paley point whose collision value lies in `𝔽₃` collides with its own cube, and a Paley point
at which `z ↦ z ^ E` is *additive on the pair `(a, 1)`* collides with its own inverse.  The latter
strictly generalises the fixed-subgroup certificate above: `a, a + 1 ∈ Fix` gives
`(a+1)^E = a + 1 = a^E + 1`, but the converse fails. -/

section FrobeniusCollision

/-- **The Paley set avoids the prime field.**  `a` and `a + 1` are non-zero by definition, and
`a = 1` would make `a + 1 = -1` a square. -/
theorem notMem_prime_field_of_mem_paleySet (h3 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F))
    {a : F} (ha : a ∈ paleySet F) : a ^ 3 ≠ a := by
  obtain ⟨ha0, -, ha10, ha1sq⟩ := ha
  intro hcube
  have hfac : a * ((a + 1) * (a - 1)) = 0 := by linear_combination hcube
  rcases mul_eq_zero.mp hfac with h | h
  · exact ha0 h
  rcases mul_eq_zero.mp h with h' | h'
  · exact ha10 h'
  · refine hnegsq ?_
    have ha1 : a = 1 := by linear_combination h'
    have hrw : a + 1 = -1 := by
      rw [ha1]
      linear_combination h3
    rwa [hrw] at ha1sq

/-- In characteristic three cubing is additive, so it is a difference-preserving map. -/
private theorem sub_pow_three (h3 : (3 : F) = 0) (x y : F) : (x - y) ^ 3 = x ^ 3 - y ^ 3 := by
  linear_combination (x * y ^ 2 - x ^ 2 * y) * h3

/-- **The Frobenius collision.**  If the collision value of a Paley point lies in the prime field,
the point collides with its own cube — which is again a Paley point, and is *different* because the
Paley set avoids `𝔽₃`. -/
theorem exists_paley_collision_of_pow_char (h3 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F))
    {a : F} (ha : a ∈ paleySet F) (hval : powDiff E a ^ 3 = powDiff E a) :
    ∃ b c : F, b ∈ paleySet F ∧ c ∈ paleySet F ∧ b ≠ c ∧ powDiff E b = powDiff E c := by
  obtain ⟨ha0, hasq, ha10, ha1sq⟩ := ha
  have hcube1 : a ^ 3 + 1 = (a + 1) ^ 3 := by linear_combination (-(a ^ 2) - a) * h3
  have hmem : a ^ 3 ∈ paleySet F := by
    refine ⟨pow_ne_zero _ ha0, ?_, ?_, ?_⟩
    · obtain ⟨s, hs⟩ := hasq
      exact ⟨s ^ 3, by rw [hs]; ring⟩
    · rw [hcube1]
      exact pow_ne_zero _ ha10
    · rw [hcube1]
      obtain ⟨s, hs⟩ := ha1sq
      exact ⟨s ^ 3, by rw [hs]; ring⟩
  have e1 : ((a + 1) ^ 3) ^ E = ((a + 1) ^ E) ^ 3 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have e2 : (a ^ 3) ^ E = (a ^ E) ^ 3 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hval3 : powDiff E (a ^ 3) = powDiff E a ^ 3 := by
    rw [powDiff, powDiff, hcube1, e1, e2, sub_pow_three h3]
  exact ⟨a, a ^ 3, ⟨ha0, hasq, ha10, ha1sq⟩, hmem,
    fun hcon => notMem_prime_field_of_mem_paleySet h3 hnegsq ⟨ha0, hasq, ha10, ha1sq⟩ hcon.symm,
    by rw [hval3, hval]⟩

/-- **The additivity collision.**  If `z ↦ z ^ E` is additive at the pair `(a, 1)`, i.e.
`(a + 1) ^ E = a ^ E + 1`, then `a` collides with `a⁻¹`, and the common value is `1`.

This strictly generalises the fixed-subgroup certificate: `a, a + 1 ∈ Fix` gives the hypothesis,
but the hypothesis is *one* equation where membership in `Fix` is two. -/
theorem exists_paley_collision_of_pow_add (h3 : (3 : F) = 0) (hnegsq : ¬ IsSquare (-1 : F))
    {a : F} (ha : a ∈ paleySet F) (hadd : (a + 1) ^ E = a ^ E + 1) :
    ∃ b c : F, b ∈ paleySet F ∧ c ∈ paleySet F ∧ b ≠ c ∧ powDiff E b = powDiff E c := by
  obtain ⟨ha0, hasq, ha10, ha1sq⟩ := ha
  have hae : a ^ E ≠ 0 := pow_ne_zero _ ha0
  have hne1 : a ≠ 1 := by
    rintro rfl
    refine hnegsq ?_
    have hrw : (1 : F) + 1 = -1 := by linear_combination h3
    rwa [hrw] at ha1sq
  have hnem1 : a ≠ -1 := by
    rintro rfl
    exact hnegsq hasq
  have hsucc : a⁻¹ + 1 = (a + 1) * a⁻¹ := by
    field_simp
    ring
  have hinvsq : IsSquare a⁻¹ := by
    obtain ⟨s, hs⟩ := hasq
    exact ⟨s⁻¹, by rw [hs, mul_inv]⟩
  have hmem : a⁻¹ ∈ paleySet F := by
    refine ⟨inv_ne_zero ha0, hinvsq, ?_, ?_⟩
    · rw [hsucc]
      exact mul_ne_zero ha10 (inv_ne_zero ha0)
    · rw [hsucc]
      obtain ⟨s, hs⟩ := ha1sq
      obtain ⟨u, hu⟩ := hinvsq
      exact ⟨s * u, by rw [hs, hu]; ring⟩
  have hva : powDiff E a = 1 := by
    rw [powDiff, hadd]
    ring
  have hvb : powDiff E a⁻¹ = 1 := by
    rw [powDiff, hsucc, mul_pow, hadd, inv_pow]
    field_simp
    ring
  refine ⟨a, a⁻¹, ⟨ha0, hasq, ha10, ha1sq⟩, hmem, ?_, by rw [hva, hvb]⟩
  intro hcon
  have hsq : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [← hcon]
      _ = 1 := mul_inv_cancel₀ ha0
  rcases mul_eq_zero.mp (show (a - 1) * (a + 1) = 0 by linear_combination hsq) with h | h
  · exact hne1 (by linear_combination h)
  · exact hnem1 (by linear_combination h)

end FrobeniusCollision

end FixedSubgroup

end PowDiff

end OddOrder.Paley
