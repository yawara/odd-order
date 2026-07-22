import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Frobenius
import OddOrder.Peterfalvi.Appendices.NearFields

/-!
# Peterfalvi Appendix C: the exceptional near-field `F_{r²,2}` (p. 138)

**Peterfalvi, Character Theory for the Odd Order Theorem, Appendix C "On Near-Fields"
(p. 138)**: the concrete instantiation of the exceptional near-field `F_{r²,2}`.

The abstract construction — `TwistData` (an order-`≤ 2` automorphism `σ` of a field `K`
plus a `σ`-invariant sign character `χ : Kˣ →* ℤ/2`, twisting the multiplication to
`x ∘ y = σ^{χ(y)}(x)·y`) and the `NearField (Twisted d)` instance — lives in
`NearFields.lean`.  This file supplies the book's actual data on `K = 𝔽_{r²}` with
`r = pⁿ`:

* `squareSignChar` — the quadratic character of a finite field, packaged as a
  homomorphism `Kˣ →* Multiplicative (ZMod 2)` (`0` on squares, `1` on non-squares);
* `halfFrobenius` — the automorphism `x ↦ x^{pⁿ}`, of order dividing `2` on a field of
  cardinality `p^{2n}`;
* `exceptionalTwistData` — the resulting `TwistData`, whose twisted multiplication is the
  book's `x ∘ y = x·y` for `y` a square, `x^{pⁿ}·y` otherwise
  (`exceptionalTwistData_twMul_of_isSquare` / `…_of_not_isSquare`).

The near-field `F_{r²,2}` itself is `Twisted (exceptionalTwistData K p n hcard)`, a
`NearField` by the generic instance.  The classification (Appendix C, Proposition 2:
these and the fields are the only finite near-fields whose multiplicative group has a
cyclic index-`2` subgroup) is `cyclic_index_two_nearField_classification` in
`NearFields.lean`.
-/

namespace OddOrder.Peterfalvi.Appendices.NearFields

/-! ### The quadratic sign character -/

section SquareSignChar

variable {K : Type*} [Field K] [Fintype K]

open scoped Classical in
/-- **The quadratic character as a `ℤ/2`-valued homomorphism** (Peterfalvi Appendix C,
p. 138): `y ↦ 0` if `y` is a square in `K`, `y ↦ 1` otherwise.  Multiplicativity is the
multiplicativity of the quadratic character of a finite field.  (In characteristic `2`
every element is a square and the character is trivial; no oddness hypothesis is
needed for the *data*.) -/
noncomputable def squareSignChar : Kˣ →* Multiplicative (ZMod 2) where
  toFun y := Multiplicative.ofAdd (if IsSquare ((y : Kˣ) : K) then (0 : ZMod 2) else 1)
  map_one' := by simp
  map_mul' a b := by
    classical
    have ha : ((a : Kˣ) : K) ≠ 0 := Units.ne_zero a
    have hb : ((b : Kˣ) : K) ≠ 0 := Units.ne_zero b
    have hab : ((a : Kˣ) : K) * ((b : Kˣ) : K) ≠ 0 := mul_ne_zero ha hb
    have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [← ofAdd_add]
    by_cases hsa : IsSquare ((a : Kˣ) : K) <;> by_cases hsb : IsSquare ((b : Kˣ) : K)
    · have hs : IsSquare (((a : Kˣ) : K) * ((b : Kˣ) : K)) := hsa.mul hsb
      simp [hsa, hsb, hs]
    · have hs : ¬IsSquare (((a : Kˣ) : K) * ((b : Kˣ) : K)) := by
        rw [← quadraticChar_neg_one_iff_not_isSquare, map_mul,
          (quadraticChar_one_iff_isSquare ha).mpr hsa,
          quadraticChar_neg_one_iff_not_isSquare.mpr hsb, one_mul]
      simp [hsa, hsb, hs]
    · have hs : ¬IsSquare (((a : Kˣ) : K) * ((b : Kˣ) : K)) := by
        rw [← quadraticChar_neg_one_iff_not_isSquare, map_mul,
          quadraticChar_neg_one_iff_not_isSquare.mpr hsa,
          (quadraticChar_one_iff_isSquare hb).mpr hsb, mul_one]
      simp [hsa, hsb, hs]
    · have hs : IsSquare (((a : Kˣ) : K) * ((b : Kˣ) : K)) := by
        rw [← quadraticChar_one_iff_isSquare hab, map_mul,
          quadraticChar_neg_one_iff_not_isSquare.mpr hsa,
          quadraticChar_neg_one_iff_not_isSquare.mpr hsb, neg_mul_neg, one_mul]
      simp [hsa, hsb, hs, h11]

theorem squareSignChar_apply_of_isSquare {y : Kˣ} (hy : IsSquare ((y : Kˣ) : K)) :
    squareSignChar y = Multiplicative.ofAdd (0 : ZMod 2) := by
  classical
  simp only [squareSignChar, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [if_pos hy]

theorem squareSignChar_apply_of_not_isSquare {y : Kˣ} (hy : ¬IsSquare ((y : Kˣ) : K)) :
    squareSignChar y = Multiplicative.ofAdd (1 : ZMod 2) := by
  classical
  simp only [squareSignChar, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [if_neg hy]

/-- Squares are preserved and reflected by a ring automorphism. -/
theorem isSquare_ringAut_iff {K : Type*} [Field K] (σ : RingAut K) {z : K} :
    IsSquare (σ z) ↔ IsSquare z := by
  constructor
  · intro h
    have := h.map (σ.symm : K →* K)
    simpa using this
  · intro h
    exact h.map (σ : K →* K)

/-- `squareSignChar` is invariant under every ring automorphism (automorphisms preserve
squares) — the `χ_σ` field of `TwistData`. -/
theorem squareSignChar_ringAut (σ : RingAut K) (y : Kˣ) :
    squareSignChar (Units.map (σ : K →* K) y) = squareSignChar y := by
  classical
  simp only [squareSignChar, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map,
    MonoidHom.coe_coe]
  exact congrArg Multiplicative.ofAdd (if_congr (isSquare_ringAut_iff σ) rfl rfl)

end SquareSignChar

/-! ### The half-Frobenius `x ↦ x^{pⁿ}` -/

section HalfFrobenius

variable (K : Type*) [Field K] [Fintype K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- **The half-Frobenius** `x ↦ x^{pⁿ}` of a finite field of characteristic `p` — for
`|K| = p^{2n}` this is the book's `x ↦ xʳ` with `r = pⁿ` (Peterfalvi Appendix C,
p. 138), the unique automorphism of order `2` when `n ≥ 1`. -/
noncomputable def halfFrobenius : RingAut K :=
  haveI : ExpChar K p := ExpChar.prime Fact.out
  (iterateFrobeniusEquiv K p n : K ≃+* K)

theorem halfFrobenius_apply (x : K) : halfFrobenius K p n x = x ^ p ^ n := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  change iterateFrobeniusEquiv K p n x = x ^ p ^ n
  rw [show ⇑(iterateFrobeniusEquiv K p n) = ⇑(iterateFrobenius K p n) from rfl,
    iterateFrobenius_def]

/-- On a field of cardinality `p^{2n}` the half-Frobenius squares to the identity —
the `σ_sq` field of `TwistData`. -/
theorem halfFrobenius_sq (hcard : Fintype.card K = p ^ (2 * n)) :
    halfFrobenius K p n ^ 2 = 1 := by
  ext x
  rw [sq, RingAut.mul_apply, RingAut.one_apply, halfFrobenius_apply, halfFrobenius_apply,
    ← pow_mul, show p ^ n * p ^ n = Fintype.card K by rw [hcard, two_mul, pow_add]]
  exact FiniteField.pow_card x

end HalfFrobenius

/-! ### The exceptional near-field `F_{r²,2}` -/

section ExceptionalNearField

variable (K : Type*) [Field K] [Fintype K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- **Peterfalvi Appendix C, the exceptional near-field `F_{r²,2}` — the twisting data**
(p. 138).  On a finite field `K` of cardinality `r² = p^{2n}` (the book's `K = 𝔽_{r²}`,
`r = pⁿ` a power of an odd prime — oddness is not needed for the construction itself),
the half-Frobenius `σ : x ↦ xʳ` and the quadratic character `χ` twist the field
multiplication to `x ∘ y = σ^{χ(y)}(x)·y`, i.e. `x·y` for `y` a square and `xʳ·y`
otherwise.  The resulting near-field `F_{r²,2}` is `Twisted (exceptionalTwistData …)`,
a `NearField` by the generic instance in `NearFields.lean`. -/
noncomputable def exceptionalTwistData (hcard : Fintype.card K = p ^ (2 * n)) :
    TwistData K where
  σ := halfFrobenius K p n
  σ_sq := halfFrobenius_sq K p n hcard
  χ := squareSignChar
  χ_σ := fun y => squareSignChar_ringAut (halfFrobenius K p n) y

/-- The book's first branch: for `y` a **square**, the twisted multiplication of
`F_{r²,2}` is the field multiplication, `x ∘ y = x·y`. -/
theorem exceptionalTwistData_twMul_of_isSquare (hcard : Fintype.card K = p ^ (2 * n))
    {y : K} (hy : IsSquare y) (x : K) :
    (exceptionalTwistData K p n hcard).twMul x y = x * y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [TwistData.twMul_zero, mul_zero]
  · have hexp : (exceptionalTwistData K p n hcard).twExp y = 0 := by
      rw [TwistData.twExp, dif_neg hy0]
      have : IsSquare ((Units.mk0 y hy0 : Kˣ) : K) := hy
      rw [show (exceptionalTwistData K p n hcard).χ = squareSignChar from rfl,
        squareSignChar_apply_of_isSquare this]
      simp
    rw [TwistData.twMul, hexp, TwistData.twAut_zero]
    simp

/-- The book's second branch: for `y` a **non-square**, the twisted multiplication of
`F_{r²,2}` applies the half-Frobenius to the left factor, `x ∘ y = xʳ·y` with
`r = pⁿ`. -/
theorem exceptionalTwistData_twMul_of_not_isSquare (hcard : Fintype.card K = p ^ (2 * n))
    {y : K} (hy : ¬IsSquare y) (x : K) :
    (exceptionalTwistData K p n hcard).twMul x y = x ^ p ^ n * y := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ ⟨0, (zero_mul 0).symm⟩)
  have hexp : (exceptionalTwistData K p n hcard).twExp y = 1 := by
    rw [TwistData.twExp, dif_neg hy0]
    have : ¬IsSquare ((Units.mk0 y hy0 : Kˣ) : K) := hy
    rw [show (exceptionalTwistData K p n hcard).χ = squareSignChar from rfl,
      squareSignChar_apply_of_not_isSquare this]
    simp
  rw [TwistData.twMul, hexp, TwistData.twAut_one,
    show (exceptionalTwistData K p n hcard).σ = halfFrobenius K p n from rfl,
    halfFrobenius_apply]

end ExceptionalNearField

/-! ### `F_{r²,2}` is not a field -/

section NotCommutative

variable (K : Type*) [Field K] [Fintype K] (p n : ℕ) [Fact p.Prime] [CharP K p]

/-- For `n ≥ 1` and `p` odd the half-Frobenius moves some **square**.  Otherwise
`σ(z)² = z²` for every `z`, so `σ z = ±z`, making `(K, +)` the union of the two additive
subgroups `{σ = id}` and `{σ = -id}`; the first is proper (a multiplicative generator
has order `p^{2n} - 1 > pⁿ - 1`), the second is proper (`σ(1) = 1 ≠ -1` as `p ≠ 2`),
and a group is never the union of two proper subgroups (the element `a + 1` with
`σ a = -a`, `a ≠ 0` lands in neither). -/
theorem exists_isSquare_halfFrobenius_ne (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hcard : Fintype.card K = p ^ (2 * n)) :
    ∃ z : K, halfFrobenius K p n (z ^ 2) ≠ z ^ 2 := by
  have hp : p.Prime := Fact.out
  have h2K : (2 : K) ≠ 0 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff K p 2).mp h))
  by_contra hcon
  push Not at hcon
  have hpm : ∀ z : K, halfFrobenius K p n z = z ∨ halfFrobenius K p n z = -z := fun z =>
    (Commute.all _ z).sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow]; exact hcon z)
  -- `σ ≠ id`: a multiplicative generator has order `p^{2n} - 1`, not dividing `pⁿ - 1`.
  have hσne : ¬∀ z : K, halfFrobenius K p n z = z := by
    intro hfix
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf g = p ^ (2 * n) - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
        Nat.card_eq_fintype_card, hcard]
    have hgval : ((g : Kˣ) : K) ^ p ^ n = ((g : Kˣ) : K) := by
      rw [← halfFrobenius_apply]; exact hfix _
    have hgpow : g ^ p ^ n = g ^ 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, pow_one]; exact hgval)
    have hple : 1 ≤ p ^ n := Nat.one_le_pow n p hp.pos
    have hdvd : orderOf g ∣ p ^ n - 1 :=
      (Nat.modEq_iff_dvd' hple).mp (pow_eq_pow_iff_modEq.mp hgpow).symm
    have ht2 : 2 ≤ p ^ n := le_trans hp.two_le (Nat.le_self_pow hn p)
    have htpos : 0 < p ^ n - 1 := by omega
    have hle := Nat.le_of_dvd htpos hdvd
    rw [hord] at hle
    have hsq : p ^ (2 * n) = p ^ n * p ^ n := by rw [two_mul, pow_add]
    have hmul : 2 * p ^ n ≤ p ^ n * p ^ n := Nat.mul_le_mul_right _ ht2
    omega
  -- an element negated by `σ`, necessarily nonzero
  obtain ⟨a, ha⟩ := not_forall.mp hσne
  have haneg : halfFrobenius K p n a = -a := (hpm a).resolve_left ha
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  -- `a + 1` is neither fixed nor negated
  have hsum := hpm (a + 1)
  rw [map_add, haneg, map_one] at hsum
  rcases hsum with h | h
  · have h' : -a = a := add_right_cancel h
    have h2a : (2 : K) * a = 0 := by
      rw [two_mul, neg_eq_iff_add_eq_zero.mp h']
    rcases mul_eq_zero.mp h2a with h2 | h2
    · exact h2K h2
    · exact ha0 h2
  · rw [neg_add] at h
    have h1 : (1 : K) = -1 := add_left_cancel h
    exact h2K (by rw [← one_add_one_eq_two, eq_neg_iff_add_eq_zero.mp h1])

/-- **The twisted multiplication of `F_{r²,2}` is not commutative** (Peterfalvi
Appendix C, p. 138): for `r = pⁿ` a power of an odd prime (`n ≥ 1`), the twist is
genuine — a square `z²` moved by the half-Frobenius and a non-square `y` do not
commute, since `z² ∘ y = (z²)ʳ·y` while `y ∘ z² = y·z²`.  Hence the exceptional branch
of Proposition 2 (`cyclic_index_two_nearField_classification`) is disjoint from the
field branch. -/
theorem exceptionalTwistData_not_comm (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hcard : Fintype.card K = p ^ (2 * n)) :
    ∃ x y : K, (exceptionalTwistData K p n hcard).twMul x y ≠
      (exceptionalTwistData K p n hcard).twMul y x := by
  obtain ⟨z, hz⟩ := exists_isSquare_halfFrobenius_ne K p n hp2 hn hcard
  have hchar2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨y, hy⟩ := FiniteField.exists_nonsquare (F := K) hchar2
  have hy0 : y ≠ 0 := fun h => hy (h ▸ ⟨0, (zero_mul (0 : K)).symm⟩)
  refine ⟨z ^ 2, y, ?_⟩
  rw [exceptionalTwistData_twMul_of_not_isSquare K p n hcard hy,
    exceptionalTwistData_twMul_of_isSquare K p n hcard (IsSquare.sq z)]
  intro h
  apply hz
  rw [halfFrobenius_apply]
  exact mul_right_cancel₀ hy0 (h.trans (mul_comm y (z ^ 2)))

/-- **The exceptional near-field `F_{r²,2}` is not a field**: the near-field
`Twisted (exceptionalTwistData …)` has non-commutative multiplication. -/
theorem exceptionalNearField_not_commutative (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hcard : Fintype.card K = p ^ (2 * n)) :
    ∃ x y : Twisted (exceptionalTwistData K p n hcard), x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := exceptionalTwistData_not_comm K p n hp2 hn hcard
  exact ⟨x, y, hxy⟩

end NotCommutative

end OddOrder.Peterfalvi.Appendices.NearFields
