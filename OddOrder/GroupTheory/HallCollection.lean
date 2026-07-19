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

/-! ## Binomial bookkeeping

Two `Nat.choose` identities drive the collecting process.  The hockey-stick
identity turns "sum over the steps of the process" into a binomial coefficient
one degree higher; its convolution refinement does the same when the steps are
*also* weighted by a binomial coefficient, which is what happens once the
conjugations occurring in the process are expanded as well.
-/

section Binomial

open Finset

/-- Hockey stick over `range`: `∑_{m < n+1} C(m, j) = C(n+1, j+1)`.
(mathlib's `Nat.sum_Icc_choose` with the vanishing terms `m < j` put back in.) -/
theorem Nat.sum_range_choose_right (n j : ℕ) :
    ∑ m ∈ range (n + 1), m.choose j = (n + 1).choose (j + 1) := by
  rw [← Nat.sum_Icc_choose n j]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro m hm
    rw [Finset.mem_Icc] at hm
    exact Finset.mem_range.mpr (by omega)
  · intro m hm hnm
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Icc, not_and, not_le] at hnm
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- **Binomial convolution.**  `∑_{i ≤ n} C(i, l) · C(n - i, j) = C(n+1, l+j+1)`.

Equivalently `z^l/(1-z)^{l+1} · z^j/(1-z)^{j+1} = z^{l+j}/(1-z)^{l+j+2}`; the
proof below is the corresponding double induction, on `l` (Pascal on the left
factor) and then on `n`. -/
theorem Nat.sum_range_choose_mul_choose (l : ℕ) :
    ∀ n j : ℕ, ∑ i ∈ range (n + 1), i.choose l * (n - i).choose j
      = (n + 1).choose (l + j + 1) := by
  induction l with
  | zero =>
      intro n j
      simp only [Nat.choose_zero_right, one_mul, Nat.zero_add]
      have hrefl := Finset.sum_range_reflect (fun i => i.choose j) (n + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [hrefl]
      exact Nat.sum_range_choose_right n j
  | succ l ih =>
      intro n j
      induction n with
      | zero =>
          have h1 : Nat.choose 1 (l + 1 + j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [h1]
      | succ n ihn =>
          rw [Finset.sum_range_succ' (fun i => i.choose (l + 1) * (n + 1 - i).choose j) (n + 1)]
          have hzero : (0 : ℕ).choose (l + 1) * (n + 1 - 0).choose j = 0 := by simp
          have hbody : ∀ i ∈ range (n + 1),
              (i + 1).choose (l + 1) * (n + 1 - (i + 1)).choose j
                = i.choose l * (n - i).choose j + i.choose (l + 1) * (n - i).choose j := by
            intro i _
            rw [show n + 1 - (i + 1) = n - i by omega, Nat.choose_succ_succ, Nat.add_mul]
          rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, hzero, Nat.add_zero,
            ih n j, ihn, show l + 1 + j + 1 = l + j + 1 + 1 by omega,
            Nat.choose_succ_succ (n + 1) (l + j + 1)]

end Binomial

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

/-! ## One-variable collection

The first genuinely *collecting* step: expanding `⁅a, bⁿ⁆` along the descending
chain of left-normed commutators `⁅a, b⁆, ⁅b, ⁅a, b⁆⁆, …` produces exactly the
binomial exponents `C(n, i)`.  This is the mechanism that makes binomial
coefficients appear in Hall's formula at all, and it is self-contained: no free
group, no basic commutators, only the fact that the iterated commutators
commute with one another (which in applications holds because they all lie in a
single abelian section `γ_k / γ_{k+1}`).
-/

section OneVariable

/-- The left-normed iterated commutator chain of `a` against `b`:
`hallIter a b 0 = a`, `hallIter a b 1 = ⁅a, b⁆`, and
`hallIter a b (i + 1) = ⁅b, hallIter a b i⁆` for `i ≥ 1`.

The `b`-on-the-left shape of the recursion is forced by mathlib's convention
`⁅g, h⁆ = g h g⁻¹ h⁻¹`: it is exactly the one for which
`b * z * b⁻¹ = ⁅b, z⁆ * z` (see `conj_eq_commutatorElement_mul`), which is the
rewriting the collection performs. -/
def hallIter (a b : G) : ℕ → G
  | 0 => a
  | 1 => ⁅a, b⁆
  | (i + 2) => ⁅b, hallIter a b (i + 1)⁆

@[simp] theorem hallIter_zero (a b : G) : hallIter a b 0 = a := rfl

@[simp] theorem hallIter_one (a b : G) : hallIter a b 1 = ⁅a, b⁆ := rfl

theorem hallIter_succ (a b : G) {i : ℕ} (hi : 1 ≤ i) :
    hallIter a b (i + 1) = ⁅b, hallIter a b i⁆ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rfl

/-- The chain descends the lower central series: `hallIter a b i ∈ γ_{i+1}` in the
book's indexing, i.e. `lowerCentralSeries i` in mathlib's. -/
theorem hallIter_mem_lowerCentralSeries (a b : G) (i : ℕ) :
    hallIter a b i ∈ (⊤ : Subgroup G).lowerCentralSeries i := by
  induction i with
  | zero => exact Subgroup.mem_top _
  | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [hallIter_one, Subgroup.top_lowerCentralSeries_one]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · rw [hallIter_succ a b hi, Subgroup.lowerCentralSeries, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) ih

/-- `⁅a, b c⁆ = ⁅a, b⁆ · (⁅a, c⁆ conjugated by `b⁻¹`)`. -/
private theorem commutatorElement_mul_right' (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]; group

/-- The rewriting the collection runs on: conjugating by `b` costs exactly one
step down the chain, `b z b⁻¹ = ⁅b, z⁆ z`. -/
theorem conj_eq_commutatorElement_mul (b z : G) : b * z * b⁻¹ = ⁅b, z⁆ * z := by
  simp only [commutatorElement_def]; group

/-- Conjugation distributes over an ordered product. -/
private theorem conj_list_prod (b : G) (l : List G) :
    b * l.prod * b⁻¹ = (l.map fun z => b * z * b⁻¹).prod := by
  induction l with
  | nil => simp
  | cons z t ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]; group

/-- An ordered product of pointwise products splits, provided every left factor
commutes with every right factor. -/
private theorem prod_map_mul_of_commute {l : List ℕ} {f g : ℕ → G}
    (h : ∀ i ∈ l, ∀ j ∈ l, Commute (g i) (f j)) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons i t ih =>
      have hgi : Commute (g i) (t.map f).prod := by
        refine Commute.list_prod_right _ _ ?_
        intro z hz
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        exact h i (by simp) j (List.mem_cons_of_mem _ hj)
      have ih' := ih fun p hp q hq =>
        h p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.prod_cons, ih']
      calc f i * g i * ((t.map f).prod * (t.map g).prod)
          = f i * (g i * (t.map f).prod * (t.map g).prod) := by group
        _ = f i * ((t.map f).prod * g i * (t.map g).prod) := by rw [hgi.eq]
        _ = f i * (t.map f).prod * (g i * (t.map g).prod) := by group

/-- Re-indexing an ordered product along `i ↦ i + 1`. -/
private theorem prod_map_range'_shift (f : ℕ → G) (s n : ℕ) :
    ((List.range' s n).map fun i => f (i + 1)).prod
      = ((List.range' (s + 1) n).map f).prod := by
  induction n generalizing s with
  | zero => simp
  | succ k ih => simp [List.range'_succ, ih]

/-- **One-variable collection.**  Let `d` run down the left-normed commutator
chain of `a` against `b` (`d 1 = ⁅a, b⁆` and `d (i+1) = ⁅b, d i⁆`), and suppose
the `d i` with `i ≥ 1` commute with one another.  Then

`⁅a, bⁿ⁆ = d₁^{C(n,1)} · d₂^{C(n,2)} ⋯ dₙ^{C(n,n)}`.

This is the one-variable case of Hall's collecting process, and the source of
the binomial exponents: passing one more `b` across the chain turns `d i` into
`d (i+1) · d i`, and Pascal's rule `C(n,i) + C(n,i-1) = C(n+1,i)` reassembles
the product.

In applications the commuting hypothesis is supplied by working modulo a term
of the lower central series, so that all the `d i` in play lie in one abelian
section; see `commutatorElement_pow_right_eq_prod_pow_choose_of_abelian`. -/
theorem commutatorElement_pow_right_eq_prod_pow_choose {a b : G} {d : ℕ → G}
    (hd1 : d 1 = ⁅a, b⁆) (hds : ∀ i, 1 ≤ i → d (i + 1) = ⁅b, d i⁆)
    (hc : ∀ i j, 1 ≤ i → 1 ≤ j → Commute (d i) (d j)) (n : ℕ) :
    ⁅a, b ^ n⁆ = ((List.range' 1 n).map fun i => d i ^ n.choose i).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      set A := ((List.range' 1 n).map fun i => d i ^ n.choose i).prod with hA
      set B := ((List.range' 1 n).map fun i => d (i + 1) ^ n.choose i).prod with hB
      -- One more `b` crosses the whole tail: `⁅a, b^(n+1)⁆ = d 1 * (b * A * b⁻¹)`.
      have hstep : ⁅a, b ^ (n + 1)⁆ = d 1 * (b * A * b⁻¹) := by
        rw [pow_succ' b n, commutatorElement_mul_right' a b (b ^ n), ih, hd1]
      -- Crossing turns `d i` into `d (i+1) * d i`, so the tail becomes `B * A`.
      have hconj : b * A * b⁻¹ = B * A := by
        rw [hA, conj_list_prod, List.map_map]
        have hpt : ((List.range' 1 n).map
              ((fun z => b * z * b⁻¹) ∘ fun i => d i ^ n.choose i))
            = (List.range' 1 n).map fun i => d (i + 1) ^ n.choose i * d i ^ n.choose i := by
          refine List.map_congr_left ?_
          intro i hi
          have hi1 : 1 ≤ i := (List.mem_range'_1.mp hi).1
          have hcj : b * d i * b⁻¹ = d (i + 1) * d i := by
            rw [conj_eq_commutatorElement_mul, hds i hi1]
          have : b * d i ^ n.choose i * b⁻¹ = (b * d i * b⁻¹) ^ n.choose i := by
            simp [conj_pow]
          simp only [Function.comp_apply, this, hcj]
          exact (hc (i + 1) i (by omega) hi1).mul_pow _
        rw [hpt]
        refine prod_map_mul_of_commute ?_
        intro i hi j hj
        have hi1 : 1 ≤ i := (List.mem_range'_1.mp hi).1
        have hj1 : 1 ≤ j := (List.mem_range'_1.mp hj).1
        exact (hc i (j + 1) hi1 (by omega)).pow_pow _ _
      -- Pascal's rule reassembles `(d 1 * B) * A` on the other side.
      have hpascal : ((List.range' 1 (n + 1)).map fun i => d i ^ (n + 1).choose i).prod
          = (d 1 * B) * A := by
        rw [← prod_map_range'_shift (fun i => d i ^ (n + 1).choose i) 0 (n + 1)]
        have hsplit : ((List.range' 0 (n + 1)).map fun j => d (j + 1) ^ (n + 1).choose (j + 1))
            = (List.range' 0 (n + 1)).map
                fun j => d (j + 1) ^ n.choose j * d (j + 1) ^ n.choose (j + 1) := by
          refine List.map_congr_left ?_
          intro j _
          rw [← pow_add, Nat.choose_succ_succ]
        rw [hsplit, prod_map_mul_of_commute (fun i _ j _ => (hc (i + 1) (j + 1)
          (by omega) (by omega)).pow_pow _ _)]
        congr 1
        · -- `∏_{j=0}^{n} d(j+1)^{C(n,j)} = d 1 * B`
          rw [List.range'_succ, List.map_cons, List.prod_cons, hB, Nat.choose_zero_right, pow_one]
        · -- `∏_{j=0}^{n} d(j+1)^{C(n,j+1)} = A`, the top slot being `C(n,n+1) = 0`
          have hcat : List.range' 0 (n + 1) = List.range' 0 n ++ [n] := by
            have h := @List.range'_append 0 n 1 1
            rw [show 0 + 1 * n = n by omega] at h
            rw [← h]; simp
          rw [hcat, List.map_append, List.prod_append]
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
            Nat.choose_succ_self, pow_zero, mul_one]
          rw [prod_map_range'_shift (fun i => d i ^ n.choose i) 0 n, hA]
      rw [hstep, hconj, hpascal, mul_assoc]

/-- **Conjugation by a power, expanded.**  The cost of conjugating `z` by `y^i` is
a product of binomial powers of the iterated commutators of `z` against `y⁻¹`:

`(y^i)⁻¹ z y^i = (e₁^{C(i,1)} ⋯ e_i^{C(i,i)})⁻¹ · z`.

This is the same one-variable collection read in the other slot (via
`⁅g, h⁆⁻¹ = ⁅h, g⁆`), and it is what turns the conjugations appearing in the
unrolled collecting process into binomial powers of fixed elements. -/
theorem conj_pow_eq_prod_pow_choose {y z : G} {e : ℕ → G}
    (he1 : e 1 = ⁅z, y⁻¹⁆) (hes : ∀ j, 1 ≤ j → e (j + 1) = ⁅y⁻¹, e j⁆)
    (hc : ∀ j l, 1 ≤ j → 1 ≤ l → Commute (e j) (e l)) (i : ℕ) :
    (y ^ i)⁻¹ * z * y ^ i
      = (((List.range' 1 i).map fun j => e j ^ i.choose j).prod)⁻¹ * z := by
  have h : ⁅z, (y⁻¹) ^ i⁆ = ((List.range' 1 i).map fun j => e j ^ i.choose j).prod :=
    commutatorElement_pow_right_eq_prod_pow_choose he1 hes hc i
  rw [← h, commutatorElement_inv, ← conj_eq_commutatorElement_mul, inv_pow, inv_inv]

end OneVariable

/-! ## Unrolling the collecting process

`pow_succ_collect` is a one-step recursion; iterating it expresses the whole
collection tail as an explicit ordered product of conjugated commutators, with
no hypotheses at all.  Together with the one-variable collection above (which
expands each individual factor into binomial powers) and the hockey-stick
identity (which sums the binomial coefficients over the steps) this is the
skeleton of Hall's formula.
-/

section Unroll

/-- The fresh commutator produced at step `m` of the collecting process:
pushing one more `x` to the left past `(x y)^m` costs exactly this. -/
def collectionCommutator (x y : G) (m : ℕ) : G := ⁅x⁻¹, ((x * y) ^ m)⁻¹⁆

@[simp] theorem collectionCommutator_zero (x y : G) : collectionCommutator x y 0 = 1 := by
  simp [collectionCommutator]

theorem collectionCommutator_mem (x y : G) (m : ℕ) :
    collectionCommutator x y m ∈ (⊤ : Subgroup G).lowerCentralSeries 1 :=
  pow_succ_collect_mem x y m

/-- The bridge to the one-variable collection: the step commutators of the
process are the single family `⁅x⁻¹, b^m⁆` for the *fixed* letter
`b = (x y)⁻¹`.  So `commutatorElement_pow_right_eq_prod_pow_choose` expands all
of them at once, with `m`-independent factors `hallIter x⁻¹ (x y)⁻¹ i`. -/
theorem collectionCommutator_eq_commutatorElement_pow (x y : G) (m : ℕ) :
    collectionCommutator x y m = ⁅x⁻¹, ((x * y)⁻¹) ^ m⁆ := by
  rw [collectionCommutator, inv_pow]

/-- **The collecting process, unrolled.**  For every `x, y` and every `n`,

`xⁿ yⁿ = (x y)ⁿ · ∏_{i=1}^{n-1} (y^i)⁻¹ · collectionCommutator x y (n - i) · y^i`,

the product taken in increasing order of `i`.  This is `pow_succ_collect`
iterated: step `m` contributes the commutator `collectionCommutator x y m`, and
each subsequent step conjugates the accumulated tail by `y` once more, so the
contribution of step `m = n - i` ends up conjugated by `y^i`.

The identity is unconditional — no nilpotency, no commutation.  All of the
remaining content of Theorem E.1 is in *sorting* this product by weight. -/
theorem pow_mul_pow_eq_pow_mul_prod_collectionCommutator (x y : G) (n : ℕ) :
    x ^ n * y ^ n = (x * y) ^ n *
      ((List.range' 1 (n - 1)).map fun i =>
        (y ^ i)⁻¹ * collectionCommutator x y (n - i) * y ^ i).prod := by
  induction n with
  | zero => simp
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at ih ⊢
      set f : ℕ → G := fun i => (y ^ i)⁻¹ * collectionCommutator x y (k + 1 - i) * y ^ i
        with hf
      set g : ℕ → G := fun i => (y ^ i)⁻¹ * collectionCommutator x y (k + 1 + 1 - i) * y ^ i
        with hg
      -- the whole old tail simply gets conjugated by `y` once more …
      have hconj := conj_list_prod (y⁻¹) ((List.range' 1 k).map f)
      simp only [inv_inv, List.map_map] at hconj
      -- … which is exactly the shift `i ↦ i + 1` of the index.
      have hshift : ((List.range' (1 + 1) k).map g).prod
          = ((List.range' 1 k).map ((fun z => y⁻¹ * z * y) ∘ f)).prod := by
        rw [← prod_map_range'_shift g 1 k]
        refine congrArg List.prod (List.map_congr_left ?_)
        intro i _
        have hsub : k + 1 + 1 - (i + 1) = k + 1 - i := by omega
        simp only [hf, hg, Function.comp_apply, hsub, pow_succ, mul_inv_rev]
        group
      -- the fresh factor is the step-`k+1` commutator, conjugated once.
      have hhead : g 1 = y⁻¹ * ⁅x⁻¹, ((x * y) ^ (k + 1))⁻¹⁆ * y := by
        simp [hg, collectionCommutator]
      rw [pow_succ_collect ih, List.range'_succ, List.map_cons, List.prod_cons, hshift,
        ← hconj, hhead]
      group

end Unroll

end OddOrder.GroupTheory
