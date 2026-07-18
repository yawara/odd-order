/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# Hall's collecting process: the general framework

P. Hall's *collecting process* turns the word `(x y)ⁿ` into `xⁿ yⁿ` times an
ordered product of commutators of increasing weight, the weight-`r` factor
carrying the binomial exponent `C(n, r)`.  The resulting identity

`xⁿ yⁿ = (x y)ⁿ · c₂^{C(n,2)} c₃^{C(n,3)} ⋯ cₙ^{C(n,n)}`,  `c_r ∈ γ_r(G)`,

is BG Theorem E.1 (Bender--Glauberman, *Local Analysis for the Odd Order
Theorem*, Appendix E), also known as the Hall--Petrescu formula.  Neither
mathlib nor this repository had any general form of it; this file collects the
`γ`-graded bookkeeping that the collecting process runs on.

BG indexes the lower central series as `G = G₁ ⊇ G₂ ⊇ ⋯`, so the book's `Gᵣ`
is mathlib's `(⊤ : Subgroup G).lowerCentralSeries (r - 1)`.

## Main definitions

* `OddOrder.GroupTheory.hallTail c n` — the *ordered* product
  `c₂^{C(n,2)} ⋯ cₙ^{C(n,n)}`, spelled as a `List.prod` over
  `List.range' 2 (n - 1) = [2, 3, …, n]` (a `Finset.prod` would need
  commutativity, which is exactly what fails here).

## Main results

* `hallTail_eq_of_eq_one_of_three_le`, `hallTail_eq_of_eq_one_of_four_le` —
  collapse of the tail when all factors beyond weight `2`, resp. `3`, are
  trivial.  These are what a class-`≤ 2`, resp. class-`≤ 3`, collection
  identity has to match.
* `pow_succ_collect` — the **exact collection recursion**.  If
  `xⁿ yⁿ = (x y)ⁿ T`, then

  `x^{n+1} y^{n+1} = (x y)^{n+1} · (⁅x⁻¹, ((x y)ⁿ)⁻¹⁆ · T)^y`.

  This is the engine of the collecting process: the new tail is the old one
  conjugated by `y`, premultiplied by one fresh commutator, and the fresh
  commutator lies in `γ₂`.  Iterating it and sorting the accumulated
  commutators by weight is Hall's process.
* `pow_succ_collect_mem` — the depth bookkeeping attached to the recursion:
  the fresh factor lies in `γ₂ = commutator G`, and conjugation preserves every
  `γ_r`.
* `exists_hallCollection_of_residue` — the **top-slot absorption reduction**:
  because the last exponent is `C(n, n) = 1`, it suffices to collect up to
  weight `n - 1` and know that the residue lies in `γ_n`.  In other words,
  Theorem E.1 for a given `n` is a statement *modulo* `γ_n`, not an exact
  identity in disguise.

## Status

The framework below is complete and `sorry`-free.  The general collection
theorem itself is **not** proved here; see
`OddOrder.BG.AppE.hallCollection` (statement, still `sorry`) and
`OddOrder.BG.AppE.hallCollection_of_class_le_three` (proved) for the current
state, and the module docstring of `OddOrder/BG/AppE_FurtherResults.lean` for
the precise obstruction.
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

/-! ## The ordered collection tail -/

section Tail

/-- The ordered product `c₂ ^ C(n,2) ⋯ cₙ ^ C(n,n)`, i.e. the right-hand tail of
Hall's collection formula (BG Theorem E.1).

The product is over `List.range' 2 (n - 1) = [2, 3, …, n]` and is *ordered*: the
`c_r` need not commute, so a `Finset.prod` would not be well defined. -/
def hallTail (c : ℕ → G) (n : ℕ) : G :=
  ((List.range' 2 (n - 1)).map fun r => c r ^ n.choose r).prod

@[simp] theorem hallTail_zero (c : ℕ → G) : hallTail c 0 = 1 := by simp [hallTail]

@[simp] theorem hallTail_one (c : ℕ → G) : hallTail c 1 = 1 := by simp [hallTail]

/-- A block of the tail all of whose indices are `≥ b` collapses to `1`, provided
`c r = 1` for every `r ≥ b`. -/
theorem hallTail_block_eq_one {c : ℕ → G} {n b m k : ℕ} (hb : b ≤ m)
    (h : ∀ r, b ≤ r → c r = 1) :
    ((List.range' m k).map fun r => c r ^ n.choose r).prod = 1 := by
  refine List.prod_eq_one ?_
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rw [h r (le_trans hb (List.mem_range'_1.mp hr).1), one_pow]

/-- If every factor of weight `≥ 3` is trivial, the tail collapses to its weight-`2`
term.  This is the shape a class-`≤ 2` collection identity must match. -/
theorem hallTail_eq_of_eq_one_of_three_le (c : ℕ → G) {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ r, 3 ≤ r → c r = 1) : hallTail c n = c 2 ^ n.choose 2 := by
  have hsplit : n - 1 = (n - 2) + 1 := by omega
  rw [hallTail, hsplit, List.range'_succ, List.map_cons, List.prod_cons,
    hallTail_block_eq_one (b := 3) (le_refl _) h, mul_one]

/-- If every factor of weight `≥ 4` is trivial, the tail collapses to its weight-`2`
and weight-`3` terms.  This is the shape a class-`≤ 3` collection identity must
match.  (For `n = 2` the weight-`3` term is absent from the product, but its
exponent `C(2,3)` is `0`, so the two sides still agree.) -/
theorem hallTail_eq_of_eq_one_of_four_le (c : ℕ → G) {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ r, 4 ≤ r → c r = 1) :
    hallTail c n = c 2 ^ n.choose 2 * c 3 ^ n.choose 3 := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · -- `n = 2`: the tail is the single factor `c₂ ^ C(2,2)`, and `C(2,3) = 0`.
    subst h2
    norm_num [hallTail, List.range'_succ]
  · -- `n ≥ 3`: peel off the weight-`2` and weight-`3` factors.
    have hs1 : n - 1 = (n - 2) + 1 := by omega
    have hs2 : n - 2 = (n - 3) + 1 := by omega
    rw [hallTail, hs1, List.range'_succ, List.map_cons, List.prod_cons, hs2,
      List.range'_succ, List.map_cons, List.prod_cons,
      hallTail_block_eq_one (b := 4) (le_refl _) h, mul_one]

/-- Splitting off the **top** slot of the tail: for `n ≥ 2`,
`hallTail c n = (c₂^{C(n,2)} ⋯ c_{n-1}^{C(n,n-1)}) · c n`, because the top
exponent is `C(n, n) = 1`. -/
theorem hallTail_eq_prefix_mul_top (c : ℕ → G) {n : ℕ} (hn : 2 ≤ n) :
    hallTail c n
      = ((List.range' 2 (n - 2)).map fun r => c r ^ n.choose r).prod * c n := by
  have hlen : n - 1 = (n - 2) + 1 := by omega
  have hcat : List.range' 2 (n - 2 + 1) = List.range' 2 (n - 2) ++ [n] := by
    have h := @List.range'_append 2 (n - 2) 1 1
    rw [show 2 + 1 * (n - 2) = n by omega] at h
    rw [← h]; simp
  rw [hallTail, hlen, hcat]
  simp

end Tail

/-! ## The collection recursion -/

section Recursion

/-- The pure group identity behind `pow_succ_collect`, with all powers abstracted
into opaque letters. -/
private theorem collect_aux (x y X Y A T : G) (h : X * Y = A * T) :
    x * X * (Y * y) = A * (x * y) * (y⁻¹ * (⁅x⁻¹, A⁻¹⁆ * T) * y) := by
  have hT : T = A⁻¹ * (X * Y) := by rw [h]; group
  subst hT
  rw [commutatorElement_def]
  group

/-- **The collection recursion** (one step of Hall's collecting process).

If `xⁿ yⁿ = (x y)ⁿ · T`, then

`x^{n+1} y^{n+1} = (x y)^{n+1} · (⁅x⁻¹, ((x y)ⁿ)⁻¹⁆ · T)^y`.

Read: pushing one more `x` to the left past `(x y)ⁿ` costs exactly one
commutator `⁅x⁻¹, ((x y)ⁿ)⁻¹⁆ ∈ γ₂`, and the whole tail then gets conjugated by
`y`.  Conjugation preserves each `γ_r`, so the *weights* of the accumulated
commutators are unchanged; Hall's process is the reordering of the accumulated
product by weight, which is where the binomial exponents come from. -/
theorem pow_succ_collect {x y T : G} {n : ℕ} (h : x ^ n * y ^ n = (x * y) ^ n * T) :
    x ^ (n + 1) * y ^ (n + 1)
      = (x * y) ^ (n + 1) * (y⁻¹ * (⁅x⁻¹, ((x * y) ^ n)⁻¹⁆ * T) * y) := by
  rw [pow_succ' x n, pow_succ y n, pow_succ (x * y) n]
  exact collect_aux x y (x ^ n) (y ^ n) ((x * y) ^ n) T h

end Recursion

/-! ## Depth bookkeeping -/

section Depth

/-- Every `γ_r` is normal, so conjugation preserves membership. -/
theorem conj_mem_lowerCentralSeries {r : ℕ} {w : G}
    (hw : w ∈ (⊤ : Subgroup G).lowerCentralSeries r) (g : G) :
    g⁻¹ * w * g ∈ (⊤ : Subgroup G).lowerCentralSeries r := by
  haveI hN : ((⊤ : Subgroup G).lowerCentralSeries r).Normal := inferInstance
  simpa [mul_assoc] using hN.conj_mem _ hw g⁻¹

/-- The two facts the recursion needs about depths: the fresh commutator produced
by `pow_succ_collect` lies in `γ₂ = G'`, and conjugating the tail by `y` keeps
every constituent in the same `γ_r`. -/
theorem pow_succ_collect_mem (x y : G) (n : ℕ) :
    ⁅x⁻¹, ((x * y) ^ n)⁻¹⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries 1 := by
  rw [Subgroup.top_lowerCentralSeries_one]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Weight addition: a commutator of a `γ_i`-element with a `γ_j`-element lies in
`γ_{i+j+1}` (mathlib indexing), i.e. `[G_i, G_j] ≤ G_{i+j}` in BG's indexing.
This is the graded law that makes the collecting process terminate. -/
theorem commutatorElement_mem_lowerCentralSeries_add {i j : ℕ} {a b : G}
    (ha : a ∈ (⊤ : Subgroup G).lowerCentralSeries i)
    (hb : b ∈ (⊤ : Subgroup G).lowerCentralSeries j) :
    ⁅a, b⁆ ∈ (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) :=
  OddOrder.Isaacs.Ch04.commutator_lowerCentralSeries_le i j
    (Subgroup.commutator_mem_commutator ha hb)

end Depth

/-! ## The top-slot absorption reduction -/

section Absorption

/-- **Top-slot absorption.**  Because the top exponent of Hall's tail is
`C(n, n) = 1`, the whole weight-`n` slot is free: to obtain the collection
formula for a given `n` it suffices to collect the weights `2, …, n - 1` and to
know that whatever residue is left over lies in `γ_n` (mathlib:
`lowerCentralSeries (n - 1)`).

So Theorem E.1 for a fixed `n` is exactly a congruence *modulo* `γ_n`; there is
no extra exactness to prove.  This is the reduction step every proof of the
collection formula uses, and it is the reason the class-`≤ k` cases close the
formula for all `n` at once. -/
theorem exists_hallCollection_of_residue {x y : G} {n : ℕ} (hn : 2 ≤ n) (c : ℕ → G)
    (hc : ∀ r, 2 ≤ r → r < n → c r ∈ (⊤ : Subgroup G).lowerCentralSeries (r - 1))
    {w : G} (hw : w ∈ (⊤ : Subgroup G).lowerCentralSeries (n - 1))
    (h : x ^ n * y ^ n = (x * y) ^ n *
      (((List.range' 2 (n - 2)).map fun r => c r ^ n.choose r).prod * w)) :
    ∃ c' : ℕ → G,
      (∀ r, 2 ≤ r → r ≤ n → c' r ∈ (⊤ : Subgroup G).lowerCentralSeries (r - 1)) ∧
      x ^ n * y ^ n = (x * y) ^ n * hallTail c' n := by
  classical
  refine ⟨Function.update c n w, ?_, ?_⟩
  · intro r hr2 hrn
    rcases eq_or_lt_of_le hrn with rfl | hlt
    · simpa using hw
    · rw [Function.update_of_ne (by omega) w c]
      exact hc r hr2 hlt
  · rw [hallTail_eq_prefix_mul_top _ hn, Function.update_self]
    -- the prefix `[2, …, n-1]` does not meet the updated index `n`
    have hpre : ((List.range' 2 (n - 2)).map
          fun r => (Function.update c n w) r ^ n.choose r).prod
        = ((List.range' 2 (n - 2)).map fun r => c r ^ n.choose r).prod := by
      refine congrArg List.prod (List.map_congr_left ?_)
      intro r hr
      have : r ≠ n := by
        have := List.mem_range'_1.mp hr
        omega
      rw [Function.update_of_ne this w c]
    rw [hpre, ← mul_assoc] at *
    exact h

end Absorption

end OddOrder.GroupTheory
