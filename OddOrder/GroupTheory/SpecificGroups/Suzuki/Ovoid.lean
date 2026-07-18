/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.RootGroup
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The anisotropic norm and point carrier of the Suzuki ovoid

For the defining field `F = Field m` and Tits twist `theta`, the fourth
coordinate of the standard affine ovoid chart is the anisotropic polynomial

`N(x,y) = x^2 * theta(x) + x*y + theta(y)`.

The ovoid carrier consists of a point at infinity and one affine point for each
element of the Suzuki root group.  This file proves the norm identities needed
by the Weyl transformation and the exact point count `q^2 + 1`.

This is shared infrastructure for the Suzuki target in **Peterfalvi, Part II,
Chapter I, Theorem A** (pp. 97-98).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

/-- The norm polynomial in the standard Suzuki ovoid coordinates. -/
noncomputable def suzukiNorm (m : ℕ) (x y : Field m) : Field m :=
  x ^ 2 * titsTwist m x + x * y + titsTwist m y

@[simp] theorem suzukiNorm_zero_zero (m : ℕ) : suzukiNorm m 0 0 = 0 := by
  simp [suzukiNorm]

/-- Applying the Tits twist to the Suzuki norm. -/
theorem titsTwist_suzukiNorm (m : ℕ) (x y : Field m) :
    titsTwist m (suzukiNorm m x y) =
      (titsTwist m x) ^ 2 * x ^ 2 + titsTwist m x * titsTwist m y + y ^ 2 := by
  rw [suzukiNorm]
  simp only [map_add, map_mul, map_pow, titsTwist_twice]

/-- The Suzuki norm is anisotropic. -/
theorem suzukiNorm_eq_zero_iff (m : ℕ) (x y : Field m) :
    suzukiNorm m x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hN
    by_cases hx : x = 0
    · subst x
      have hyθ : titsTwist m y = 0 := by
        simpa [suzukiNorm] using hN
      have hy : y = 0 := by
        apply (titsTwist m).injective
        simpa using hyθ
      exact ⟨rfl, hy⟩
    · exfalso
      let z : Field m := y / (x * titsTwist m x)
      have hθx : titsTwist m x ≠ 0 := (map_ne_zero (titsTwist m)).2 hx
      have hden : x * titsTwist m x ≠ 0 := mul_ne_zero hx hθx
      have hyz : y = z * (x * titsTwist m x) := by
        dsimp [z]
        exact (div_mul_cancel₀ y hden).symm
      have hfactor :
          suzukiNorm m x y =
            (x ^ 2 * titsTwist m x) * (1 + z + titsTwist m z) := by
        rw [hyz, suzukiNorm]
        simp only [map_mul, titsTwist_twice]
        ring
      have hbase : x ^ 2 * titsTwist m x ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 hx) hθx
      have hsum : 1 + z + titsTwist m z = 0 := by
        have hprod :
            (x ^ 2 * titsTwist m x) * (1 + z + titsTwist m z) = 0 := by
          rw [← hfactor]
          exact hN
        exact (mul_eq_zero.mp hprod).resolve_left hbase
      have hθz : titsTwist m z = z + 1 := by
        have h := CharTwo.add_eq_zero.mp hsum
        simpa [add_comm] using h.symm
      have hzsq : z ^ 2 = z := by
        have h := congrArg (titsTwist m) hθz
        simp only [titsTwist_twice, map_add, map_one] at h
        rw [hθz] at h
        simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using h
      have hz01 : z = 0 ∨ z = 1 := by
        have hzprod : z * (z + 1) = 0 := by
          rw [mul_add, mul_one, ← pow_two, hzsq, CharTwo.add_self_eq_zero]
        rcases mul_eq_zero.mp hzprod with hz | hz
        · exact Or.inl hz
        · exact Or.inr (CharTwo.add_eq_zero.mp hz)
      rcases hz01 with hz | hz
      · rw [hz, map_zero, zero_add] at hθz
        exact zero_ne_one hθz
      · rw [hz, map_one, CharTwo.add_self_eq_zero] at hθz
        exact one_ne_zero hθz
  · rintro ⟨rfl, rfl⟩
    exact suzukiNorm_zero_zero m

/-- The reciprocal-coordinate identity for the Suzuki norm. -/
theorem suzukiNorm_reciprocal (m : ℕ) (x y : Field m) :
    suzukiNorm m (y / suzukiNorm m x y) (x / suzukiNorm m x y) =
      (suzukiNorm m x y)⁻¹ := by
  let n := suzukiNorm m x y
  by_cases hn : n = 0
  · have hxy : x = 0 ∧ y = 0 := (suzukiNorm_eq_zero_iff m x y).mp hn
    rcases hxy with ⟨rfl, rfl⟩
    simp [suzukiNorm]
  · have hθn : titsTwist m n ≠ 0 := (map_ne_zero (titsTwist m)).2 hn
    change suzukiNorm m (y / n) (x / n) = n⁻¹
    rw [suzukiNorm]
    simp only [map_div₀]
    field_simp [hn, hθn]
    rw [show n = suzukiNorm m x y by rfl, titsTwist_suzukiNorm, suzukiNorm]
    ring_nf
    have h2 : (2 : Field m) = 0 := CharTwo.two_eq_zero
    have h3 : (3 : Field m) = 1 := by
      calc
        (3 : Field m) = 2 + 1 := by norm_num
        _ = 0 + 1 := by rw [h2]
        _ = 1 := zero_add 1
    simp only [h2, h3, mul_zero, mul_one, add_zero]


/-- Evaluate the Suzuki norm on root-group coordinates. -/
noncomputable def RootGroup.suzukiNorm {m : ℕ} (u : RootGroup m) : Field m :=
  OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm m u.fst u.snd

@[simp] theorem RootGroup.suzukiNorm_mk {m : ℕ} (x y : Field m) :
    (RootGroup.mk x y).suzukiNorm = OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm m x y :=
  rfl

/-- A root-group coordinate pair has zero Suzuki norm exactly at the identity. -/
theorem RootGroup.suzukiNorm_eq_zero_iff_eq_one {m : ℕ} (u : RootGroup m) :
    u.suzukiNorm = 0 ↔ u = 1 := by
  rw [RootGroup.suzukiNorm,
    OddOrder.GroupTheory.SpecificGroups.Suzuki.suzukiNorm_eq_zero_iff]
  constructor
  · rintro ⟨hfst, hsnd⟩
    ext
    · simpa only [RootGroup.fst_one] using hfst
    · simpa only [RootGroup.snd_one] using hsnd
  · rintro rfl
    exact ⟨RootGroup.fst_one, RootGroup.snd_one⟩

/-- The point carrier of the standard Suzuki ovoid: one point at infinity and
one affine point for each root-group coordinate pair. -/
abbrev Ovoid (m : ℕ) := Option (RootGroup m)

namespace Ovoid

variable {m : ℕ}

/-- The distinguished point at infinity of the Suzuki ovoid. -/
def infinity (m : ℕ) : Ovoid m := none

/-- The affine ovoid point indexed by a root-group coordinate pair. -/
def affine (u : RootGroup m) : Ovoid m := some u

/-- The affine ovoid point with explicit field coordinates. -/
def affineMk (x y : Field m) : Ovoid m := affine ⟨x, y⟩

@[simp] theorem affineMk_eq (x y : Field m) :
    affineMk x y = affine (RootGroup.mk x y) :=
  rfl

@[simp] theorem affine_inj {u v : RootGroup m} : affine u = affine v ↔ u = v :=
  Option.some_inj

theorem affine_ext {u v : RootGroup m}
    (hfst : u.fst = v.fst) (hsnd : u.snd = v.snd) : affine u = affine v :=
  congrArg affine (RootGroup.ext hfst hsnd)

theorem affine_injective : Function.Injective (affine : RootGroup m → Ovoid m) :=
  fun _ _ h => affine_inj.mp h

@[simp] theorem affine_ne_infinity (u : RootGroup m) : affine u ≠ infinity m :=
  Option.some_ne_none u

@[simp] theorem infinity_ne_affine (u : RootGroup m) : infinity m ≠ affine u :=
  (Option.some_ne_none u).symm

@[simp] theorem affineMk_ne_infinity (x y : Field m) : affineMk x y ≠ infinity m :=
  affine_ne_infinity _

@[simp] theorem infinity_ne_affineMk (x y : Field m) : infinity m ≠ affineMk x y :=
  infinity_ne_affine _

@[simp] theorem affineMk_inj {x y x' y' : Field m} :
    affineMk x y = affineMk x' y' ↔ x = x' ∧ y = y' := by
  simp only [affineMk, affine_inj, RootGroup.mk.injEq]

/-- Every ovoid point is either the point at infinity or a unique affine point. -/
theorem eq_infinity_or_eq_affine (p : Ovoid m) :
    p = infinity m ∨ ∃ u : RootGroup m, p = affine u := by
  cases p with
  | none => exact Or.inl rfl
  | some u => exact Or.inr ⟨u, rfl⟩

/-- Case analysis for the point at infinity and affine ovoid points. -/
@[elab_as_elim]
def cases {C : Ovoid m → Sort*}
    (hinfinity : C (infinity m)) (haffine : ∀ u : RootGroup m, C (affine u)) :
    ∀ p : Ovoid m, C p
  | none => hinfinity
  | some u => haffine u

/-- The ovoid carrier is equivalent to an optional pair of field coordinates. -/
def equivOptionProd (m : ℕ) : Ovoid m ≃ Option (Field m × Field m) :=
  Equiv.optionCongr (RootGroup.equivProd m)

@[simp] theorem equivOptionProd_infinity (m : ℕ) :
    equivOptionProd m (infinity m) = none :=
  rfl

@[simp] theorem equivOptionProd_affine (u : RootGroup m) :
    equivOptionProd m (affine u) = some (u.fst, u.snd) :=
  rfl

/-- The standard Suzuki ovoid has exactly `2 ^ (2 * (2m+1)) + 1` points. -/
theorem natCard (m : ℕ) :
    Nat.card (Ovoid m) = 2 ^ (2 * (2 * m + 1)) + 1 := by
  rw [Finite.card_option, RootGroup.natCard]

/-- An enumeration of the standard Suzuki ovoid by an initial finite interval. -/
noncomputable def equivFin (m : ℕ) :
    Ovoid m ≃ Fin (2 ^ (2 * (2 * m + 1)) + 1) :=
  Finite.equivFinOfCardEq (natCard m)

end Ovoid

end OddOrder.GroupTheory.SpecificGroups.Suzuki
