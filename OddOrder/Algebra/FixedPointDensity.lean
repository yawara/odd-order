/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Aut
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

/-!
# An endomorphism fixing more than half the points is the identity

Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000), Part II,
Ch. IV §4, p. 134, closes the chapter like this:

> Let `X ∈ F − {0, a^{2r}, a^{2r} + 1}`.  Writing (10) with `X + 1` in place of `X` and
> subtracting (10) from the result, we see that `X^μ = X`.  It follows that `μ = 1`
> since `μ` has odd order and, if `μ ≠ 1`, then `|F| > 8`.

The book reaches `μ = 1` from "`μ` fixes all but three elements" using the odd order of
`μ`.  That detour is unnecessary: the fixed points of an *additive* map already form a
subgroup, so a proper fixed-point set misses at least half of the group.  Fixing more
than half the points therefore forces the identity, with no hypothesis on the order and
none on the multiplicative structure.

For the book's situation — `|F| = q` and three exceptional points — the hypothesis reads
`6 < q`, i.e. `q ≥ 8`, which is exactly the bound the book quotes.

## Main results

* `fixedAddSubgroup` — the fixed points of an additive map, as an additive subgroup.
* `eq_id_of_fixes_compl` — an additive map fixing everything outside a set `S` with
  `2 |S| < |A|` is the identity.
* `RingEquiv.eq_refl_of_fixes_compl` — the same for a ring automorphism.
-/

set_option autoImplicit false

namespace OddOrder.FiniteField

variable {A : Type*} [AddGroup A]

/-- **The fixed points of an additive map form a subgroup.** -/
def fixedAddSubgroup (μ : A →+ A) : AddSubgroup A where
  carrier := {x | μ x = x}
  add_mem' := fun {a b} ha hb => by
    change μ (a + b) = a + b
    rw [map_add, show μ a = a from ha, show μ b = b from hb]
  zero_mem' := map_zero μ
  neg_mem' := fun {a} ha => by
    change μ (-a) = -a
    rw [map_neg, show μ a = a from ha]

@[simp] theorem mem_fixedAddSubgroup {μ : A →+ A} {x : A} :
    x ∈ fixedAddSubgroup μ ↔ μ x = x := Iff.rfl

/-- **An additive map fixing more than half the points is the identity.**

Its fixed points form a subgroup (`fixedAddSubgroup`); a proper subgroup has index at
least `2`, so it misses at least half the group.  Hence a fixed-point set whose
complement is smaller than half is everything.

This is the closing step of Peterfalvi Part II, Ch. IV §4 (p. 134), where `S` has three
elements and `A` is the field `F` of order `q ≥ 8`. -/
theorem eq_id_of_fixes_compl [Finite A] (μ : A →+ A) (S : Finset A)
    (hfix : ∀ x : A, x ∉ S → μ x = x) (hcard : 2 * S.card < Nat.card A) (x : A) :
    μ x = x := by
  classical
  set K := fixedAddSubgroup μ
  -- the complement of the fixed subgroup is contained in `S`
  have hsub : ((K : Set A))ᶜ ⊆ (↑S : Set A) := by
    intro y hy
    by_contra hyS
    exact hy (hfix y (by simpa using hyS))
  have hcompl : ((K : Set A))ᶜ.ncard ≤ S.card := by
    rw [← Set.ncard_coe_finset S]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hsplit : (K : Set A).ncard + ((K : Set A))ᶜ.ncard = Nat.card A :=
    Set.ncard_add_ncard_compl _
  have hKcard : (K : Set A).ncard = Nat.card ↥K := (Nat.card_coe_set_eq _).symm
  -- a proper subgroup would have index at least two
  have htop : K = ⊤ := by
    by_contra hne
    have hidx : Nat.card ↥K * K.index = Nat.card A := K.card_mul_index
    have hidx1 : K.index ≠ 1 := fun hc => hne (AddSubgroup.index_eq_one.mp hc)
    have hidx0 : K.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    have hidx2 : 2 ≤ K.index := by omega
    have hle : 2 * Nat.card ↥K ≤ Nat.card A := by
      calc 2 * Nat.card ↥K ≤ K.index * Nat.card ↥K := by
            exact Nat.mul_le_mul_right _ hidx2
        _ = Nat.card A := by rw [mul_comm]; exact hidx
    rw [hKcard] at hsplit
    omega
  have : x ∈ K := by rw [htop]; exact AddSubgroup.mem_top x
  exact this

/-- **A ring automorphism fixing more than half the points is the identity.**

Only additivity is used — see `eq_id_of_fixes_compl`. -/
theorem _root_.RingEquiv.eq_refl_of_fixes_compl {R : Type*} [Ring R] [Finite R]
    (μ : R ≃+* R) (S : Finset R) (hfix : ∀ x : R, x ∉ S → μ x = x)
    (hcard : 2 * S.card < Nat.card R) :
    μ = RingEquiv.refl R :=
  RingEquiv.ext (eq_id_of_fixes_compl (μ : R ≃+ R).toAddMonoidHom S hfix hcard)

/-- **An automorphism of odd order whose square fixes more than half the points is
trivial** (Peterfalvi Part II, Ch. IV §4, p. 134).

The last step of Ch. IV: the semilinear automorphism `μ` attached to `η` satisfies
`X^{μ²} = X` off a three-element set, and `|F| ≥ 8`, so `μ² = 1`; `μ` having odd order it
is trivial, whence `η ∈ W` and `h(ω) ∈ W`. -/
theorem _root_.RingEquiv.eq_one_of_odd_orderOf_of_sq_fixes_compl {R : Type*} [Ring R]
    [Finite R] (μ : RingAut R) (hodd : Odd (orderOf μ)) (S : Finset R)
    (hfix : ∀ x : R, x ∉ S → μ (μ x) = x) (hcard : 2 * S.card < Nat.card R) :
    μ = 1 := by
  have hsq : μ * μ = 1 := by
    have h := RingEquiv.eq_refl_of_fixes_compl ((μ * μ : RingAut R) : R ≃+* R) S
      (fun x hx => hfix x hx) hcard
    exact h
  have hdvd : orderOf μ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  have h1 : orderOf μ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd (h ▸ hodd) (by decide)
  exact orderOf_eq_one_iff.mp h1

/-- **The step that pins `μ²` to the identity** (Peterfalvi Part II, Ch. IV §4, p. 134,
between (10) and the end).

Equation (10) reads `(c + X^μ) X = (c + X^{μ²}) X^μ` with `c = ζ + ζ⁻¹`.  Writing it at
`X + 1` as well and subtracting, every quadratic term cancels and what is left is
`X^{μ²} = X`.  (The cancellation needs no hypothesis on the characteristic, though the
book's ring is `𝐅_{2^m}`.)

The book applies this for `X ∉ {0, α^{2τ}, α^{2τ} + 1}`, so `μ²` fixes all but three
points; `RingEquiv.eq_one_of_odd_orderOf_of_sq_fixes_compl` then gives `μ = 1`. -/
theorem sq_apply_eq_of_relation {F : Type*} [CommRing F] (μ : RingAut F) (c X : F)
    (h1 : (c + μ X) * X = (c + μ (μ X)) * μ X)
    (h2 : (c + μ (X + 1)) * (X + 1) = (c + μ (μ (X + 1))) * μ (X + 1)) :
    μ (μ X) = X := by
  have hmu1 : μ (X + 1) = μ X + 1 := by rw [map_add, map_one]
  have hmu2 : μ (μ X + 1) = μ (μ X) + 1 := by rw [map_add, map_one]
  rw [hmu1] at h2
  rw [hmu2] at h2
  linear_combination h1 - h2

end OddOrder.FiniteField
