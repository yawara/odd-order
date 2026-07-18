/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.Field
import Mathlib.GroupTheory.PGroup

/-!
# The Hermitian root group and unital for `PSU(3,q)`

For `q = 2 ^ n`, this file constructs the standard unitary root group on the
Hermitian affine coordinates

`{(a, b) in GF(q²)² | b + star b = a * star a}`.

Its multiplication is

`(a, b) * (c, d) = (a + c, b + d + a * star c)`.

This is Peterfalvi Part II, Chapter III §3, where `phi(x,y) = x * y^q`.

The group laws are proved directly from these coordinates.  Every fiber over
the first coordinate has exactly `q` elements, so the root group has order
`q³`; adjoining one point at infinity gives the Hermitian unital carrier of
degree `q³ + 1`.

This is shared infrastructure for **Peterfalvi, Part II, Chapter I §3,
Lemma 1 and Proposition 1(c)** (pp. 104–106).  Peterfalvi cites Huppert,
Kapitel II, Satz 10.12 (p. 242), for the standard unitary action.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

noncomputable section

set_option maxHeartbeats 800000 in
-- Reducing the canonical finite-field extension needs additional typeclass normalization.
/-- The standard Hermitian root group for the unitary group in characteristic two. -/
@[ext]
structure RootGroup (n : ℕ) where
  fst : Field n
  snd : Field n
  condition : snd + star snd = fst * star fst

instance (n : ℕ) : Finite (RootGroup n) :=
  Finite.of_injective (fun u => (u.fst, u.snd)) fun x y h => by
    ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

namespace RootGroup

variable {n : ℕ}

instance (n : ℕ) : Mul (RootGroup n) where
  mul x y :=
    { fst := x.fst + y.fst
      snd := x.snd + y.snd + x.fst * star y.fst
      condition := by
        simp only [star_add, star_mul, star_star]
        have hx := x.condition
        have hy := y.condition
        linear_combination hx + hy }

instance (n : ℕ) : One (RootGroup n) where
  one :=
    { fst := 0
      snd := 0
      condition := by simp }

instance (n : ℕ) : Inv (RootGroup n) where
  inv x :=
    { fst := x.fst
      snd := x.snd + x.fst * star x.fst
      condition := by
        simp only [star_add, star_mul, star_star]
        have hx := x.condition
        calc
          x.snd + x.fst * star x.fst +
              (star x.snd + x.fst * star x.fst) =
              (x.snd + star x.snd) +
                (x.fst * star x.fst + x.fst * star x.fst) := by ring
          _ = x.fst * star x.fst := by
            rw [hx, CharTwo.add_self_eq_zero, add_zero] }

@[simp]
theorem fst_mul (x y : RootGroup n) : (x * y).fst = x.fst + y.fst := rfl

@[simp]
theorem snd_mul (x y : RootGroup n) :
    (x * y).snd = x.snd + y.snd + x.fst * star y.fst := rfl

@[simp]
theorem fst_one : (1 : RootGroup n).fst = 0 := rfl

@[simp]
theorem snd_one : (1 : RootGroup n).snd = 0 := rfl

@[simp]
theorem fst_inv (x : RootGroup n) : x⁻¹.fst = x.fst := rfl

@[simp]
theorem snd_inv (x : RootGroup n) :
    x⁻¹.snd = x.snd + x.fst * star x.fst := rfl

instance (n : ℕ) : Group (RootGroup n) where
  mul_assoc x y z := by
    ext
    · simp only [fst_mul]
      exact add_assoc _ _ _
    · simp only [snd_mul, fst_mul, star_add]
      ring
  one_mul x := by
    ext <;> simp
  mul_one x := by
    ext <;> simp
  inv_mul_cancel x := by
    ext
    · exact CharTwo.add_self_eq_zero _
    · simp only [snd_mul, snd_inv, fst_inv]
      change (x.snd + x.fst * star x.fst) + x.snd +
          x.fst * star x.fst = 0
      calc
        (x.snd + x.fst * star x.fst) + x.snd + x.fst * star x.fst =
            (x.snd + x.snd) +
              (x.fst * star x.fst + x.fst * star x.fst) := by ring
        _ = 0 := by
          rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]

/-- Root coordinates are a dependent sum of the Hermitian trace fibers. -/
def equivSigma (n : ℕ) :
    RootGroup n ≃ Σ a : Field n, {b : Field n // b + star b = a * star a} where
  toFun u := ⟨u.fst, ⟨u.snd, u.condition⟩⟩
  invFun u := ⟨u.1, u.2.1, u.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Hermitian root group has exact order `q³ = 2 ^ (3 * n)`. -/
theorem natCard (n : ℕ) (hn : 0 < n) :
    Nat.card (RootGroup n) = 2 ^ (3 * n) := by
  letI := Fintype.ofFinite (Field n)
  rw [Nat.card_congr (equivSigma n), Nat.card_sigma]
  simp_rw [natCard_add_star_eq_mul_star n hn]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCard_field n hn, nsmul_eq_mul]
  change 2 ^ (2 * n) * 2 ^ n = 2 ^ (3 * n)
  rw [← pow_add]
  congr 1
  omega

/-- The Hermitian root group is a `2`-group. -/
theorem isPGroup (n : ℕ) (hn : 0 < n) : IsPGroup 2 (RootGroup n) :=
  IsPGroup.of_card (natCard n hn)

end RootGroup

/-- The affine Hermitian root coordinates together with their point at infinity. -/
abbrev Unital (n : ℕ) := Option (RootGroup n)

namespace Unital

variable {n : ℕ}

/-- The distinguished point at infinity of the Hermitian unital. -/
def infinity (n : ℕ) : Unital n := none

/-- An affine Hermitian point. -/
def affine (u : RootGroup n) : Unital n := some u

@[simp]
theorem affine_ne_infinity (u : RootGroup n) : affine u ≠ infinity n :=
  Option.some_ne_none u

@[simp]
theorem infinity_ne_affine (u : RootGroup n) : infinity n ≠ affine u :=
  (Option.some_ne_none u).symm

/-- The Hermitian unital has exact degree `q³ + 1 = 2 ^ (3 * n) + 1`. -/
theorem natCard (n : ℕ) (hn : 0 < n) :
    Nat.card (Unital n) = 2 ^ (3 * n) + 1 := by
  rw [Finite.card_option, RootGroup.natCard n hn]

end Unital

end


end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
