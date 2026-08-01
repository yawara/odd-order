/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Ring.Equiv

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

end OddOrder.FiniteField
