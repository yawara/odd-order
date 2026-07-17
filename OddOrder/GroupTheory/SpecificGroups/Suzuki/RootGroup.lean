/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki.Field
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The root group of a Suzuki group

For the defining field `F = Field m` and Tits twist `θ`, the Suzuki root group is
the set `F × F` with multiplication

`(x, y) * (u, v) = (x + u, y + v + u * θ(x))`.

This is the ovoid-coordinate parametrization `y = x θ(x) + b` used by the
standard points `[1, x, y, N(x,y)]`.

It has order `|F|²`, exponent four, and the coordinate line `{(0, b)}` is a
central subgroup consisting of involutions.  This is shared infrastructure for
the Suzuki target in **Peterfalvi, Part II, Chapter I, Theorem A** (pp. 97–98).
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.Suzuki

/-- The two-coordinate carrier of the Suzuki root group. -/
@[ext]
structure RootGroup (m : ℕ) where
  fst : Field m
  snd : Field m

instance (m : ℕ) : Finite (RootGroup m) :=
  Finite.of_injective (fun x => (x.fst, x.snd)) fun x y h => by
    ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

namespace RootGroup

variable {m : ℕ}

noncomputable instance : Mul (RootGroup m) where
  mul x y := ⟨x.fst + y.fst, x.snd + y.snd + y.fst * titsTwist m x.fst⟩

noncomputable instance : One (RootGroup m) where
  one := ⟨0, 0⟩

noncomputable instance : Inv (RootGroup m) where
  inv x := ⟨x.fst, x.snd + x.fst * titsTwist m x.fst⟩

/-- Multiplication in root-group coordinates. -/
theorem mul_def (x y : RootGroup m) :
    x * y = ⟨x.fst + y.fst, x.snd + y.snd + y.fst * titsTwist m x.fst⟩ :=
  rfl

/-- The identity in root-group coordinates. -/
theorem one_def : (1 : RootGroup m) = ⟨0, 0⟩ :=
  rfl

/-- Inversion in root-group coordinates. -/
theorem inv_def (x : RootGroup m) :
    x⁻¹ = ⟨x.fst, x.snd + x.fst * titsTwist m x.fst⟩ :=
  rfl

@[simp] theorem fst_mul (x y : RootGroup m) : (x * y).fst = x.fst + y.fst := rfl

@[simp] theorem snd_mul (x y : RootGroup m) :
    (x * y).snd = x.snd + y.snd + y.fst * titsTwist m x.fst := rfl

@[simp] theorem fst_one : (1 : RootGroup m).fst = 0 := rfl

@[simp] theorem snd_one : (1 : RootGroup m).snd = 0 := rfl

@[simp] theorem fst_inv (x : RootGroup m) : x⁻¹.fst = x.fst := rfl

@[simp] theorem snd_inv (x : RootGroup m) :
    x⁻¹.snd = x.snd + x.fst * titsTwist m x.fst := rfl

/-- The coordinate multiplication defines a group. -/
noncomputable instance : Group (RootGroup m) where
  mul_assoc x y z := by
    ext
    · simp only [fst_mul]
      exact add_assoc _ _ _
    · simp only [snd_mul, fst_mul, map_add, mul_add, add_mul]
      ring
  one_mul x := by
    ext <;> simp
  mul_one x := by
    ext <;> simp
  inv_mul_cancel x := by
    ext
    · exact CharTwo.add_self_eq_zero _
    · change (x.snd + x.fst * titsTwist m x.fst) + x.snd +
        x.fst * titsTwist m x.fst = 0
      calc
        (x.snd + x.fst * titsTwist m x.fst) + x.snd +
            x.fst * titsTwist m x.fst =
            (x.snd + x.snd) +
              (x.fst * titsTwist m x.fst + x.fst * titsTwist m x.fst) := by abel
        _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]

/-- The square of `(a,b)` is `(0, a θ(a))`. -/
theorem sq_eq (x : RootGroup m) :
    x ^ 2 = ⟨0, x.fst * titsTwist m x.fst⟩ := by
  rw [pow_two]
  ext
  · exact CharTwo.add_self_eq_zero _
  · change x.snd + x.snd + x.fst * titsTwist m x.fst =
      x.fst * titsTwist m x.fst
    rw [CharTwo.add_self_eq_zero, zero_add]

/-- An element squares to one exactly when its first coordinate vanishes. -/
theorem sq_eq_one_iff (x : RootGroup m) : x ^ 2 = 1 ↔ x.fst = 0 := by
  constructor
  · intro hx
    have hprod : x.fst * titsTwist m x.fst = 0 := by
      have := congrArg RootGroup.snd hx
      simpa [sq_eq] using this
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · apply (titsTwist m).injective
      simpa using h
  · intro hx
    rw [sq_eq]
    ext <;> simp [hx]

/-- Every element of the root group has fourth power one. -/
theorem pow_four_eq_one (x : RootGroup m) : x ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by omega, pow_mul, sq_eq, sq_eq]
  ext <;> simp

/-- The central coordinate line `{(0,b)}`. -/
noncomputable def centerLine (m : ℕ) : Subgroup (RootGroup m) where
  carrier := {x | x.fst = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy
  inv_mem' := by
    intro x hx
    exact hx

@[simp] theorem mem_centerLine (x : RootGroup m) : x ∈ centerLine m ↔ x.fst = 0 :=
  Iff.rfl

@[simp] theorem mk_mem_centerLine (b : Field m) :
    (⟨0, b⟩ : RootGroup m) ∈ centerLine m :=
  rfl

/-- The coordinate line lies in the center of the root group. -/
theorem centerLine_le_center : centerLine m ≤ Subgroup.center (RootGroup m) := by
  intro z hz
  have hz0 : z.fst = 0 := hz
  rw [Subgroup.mem_center_iff]
  intro x
  ext
  · simp [hz0]
  · simp [hz0, add_comm]

/-- Every member of the central coordinate line has square one. -/
theorem sq_eq_one_of_mem_centerLine {x : RootGroup m} (hx : x ∈ centerLine m) :
    x ^ 2 = 1 :=
  (sq_eq_one_iff x).2 hx

/-- The square of every root-group element belongs to the central coordinate line. -/
theorem sq_mem_centerLine (x : RootGroup m) : x ^ 2 ∈ centerLine m := by
  rw [mem_centerLine, sq_eq]

/-- The central coordinate line is equivalent to the additive defining field. -/
noncomputable def centerLineEquivField (m : ℕ) : centerLine m ≃ Field m where
  toFun x := x.1.snd
  invFun b := ⟨⟨0, b⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    ext
    · exact x.2.symm
    · rfl
  right_inv _ := rfl

/-- The central coordinate line has order `2 ^ (2m+1)`. -/
theorem natCard_centerLine (m : ℕ) :
    Nat.card (centerLine m) = 2 ^ (2 * m + 1) := by
  rw [Nat.card_congr (centerLineEquivField m), natCard_field]

/-- The root-group carrier is equivalent to two copies of the defining field. -/
def equivProd (m : ℕ) : RootGroup m ≃ Field m × Field m where
  toFun x := (x.fst, x.snd)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The root group has exact order `2 ^ (2 * (2m+1))`. -/
theorem natCard (m : ℕ) : Nat.card (RootGroup m) = 2 ^ (2 * (2 * m + 1)) := by
  rw [Nat.card_congr (equivProd m), Nat.card_prod, natCard_field, ← pow_add]
  congr 1
  omega

/-- The Suzuki root group is a `2`-group. -/
theorem isPGroup (m : ℕ) : IsPGroup 2 (RootGroup m) :=
  IsPGroup.of_card (natCard m)

/-- The central line is the additive defining field, as a multiplicative group. -/
noncomputable def centerLineMulEquivField (m : Nat) :
    MulEquiv (centerLine m) (Multiplicative (Field m)) where
  toFun x := Multiplicative.ofAdd x.1.snd
  invFun b := ⟨⟨0, Multiplicative.toAdd b⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    ext
    · exact x.2.symm
    · rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change (x * y : RootGroup m).snd = x.1.snd + y.1.snd
    have hx0 : x.1.fst = 0 := x.2
    have hy0 : y.1.fst = 0 := y.2
    simp [hx0, hy0]

end RootGroup

end OddOrder.GroupTheory.SpecificGroups.Suzuki
