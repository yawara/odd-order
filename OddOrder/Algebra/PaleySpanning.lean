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

end PowDiff

end OddOrder.Paley
