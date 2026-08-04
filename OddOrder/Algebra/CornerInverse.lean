/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Nilpotent.Basic
import OddOrder.Algebra.JacobsonCentralSubring

/-!
# Inverting in a corner — Navarro (5.4)

**Navarro (5.4).**  Let `f ∈ 𝒪G` be an idempotent and let `x ∈ f(𝒪G)f` reduce to `f` modulo the
maximal ideal.  Then `x` is invertible in the corner `f(𝒪G)f`.

Navarro proves this by making `f(𝒪G)f` a ring with identity `f`, checking it is finite over the
central subring `f𝒪`, and applying (5.3) there.  Formalising a ring whose identity is `f` is
awkward, and it is not needed: put

`u = x + (1 - f)`.

Then `u - 1 = x - f` lies in `𝔪·𝒪G ⊆ J(𝒪G)` — this is (5.3) applied to `𝒪G` itself — so `u` is a
unit of `𝒪G`, and one checks `f u = u f = x`.  The corner inverse is then simply `f u⁻¹ f`.  The
only ring theory used is that `1 + J` consists of units, proved here for a possibly
noncommutative ring since mathlib's version assumes commutativity.

The unit hypothesis is isolated as `exists_corner_inverse_of_isUnit`, since (5.5) needs the same
argument in characteristic `p`, where `u` is a unit because `u - 1` is *nilpotent* rather than in
the radical.

## Main results

* `OddOrder.isUnit_one_add_of_mem_ringJacobson`
* `OddOrder.exists_corner_inverse_of_isUnit` — the core
* `OddOrder.map_maximalIdeal_le_ringJacobson`
* `OddOrder.exists_corner_inverse` — Navarro (5.4)
* `OddOrder.exists_corner_inverse_of_isNilpotent` — the characteristic-`p` variant
-/

namespace OddOrder

/-- **`1 + J(A)` consists of units**, for a possibly noncommutative ring.  A left inverse `z` of
`1 + j` is itself of the form `1 + J`, hence has a left inverse; that forces `z` to be a
two-sided inverse.  mathlib's `Ideal.isUnit_of_sub_one_mem_jacobson_bot` assumes commutativity. -/
theorem isUnit_one_add_of_mem_ringJacobson {A : Type*} [Ring A] {j : A}
    (hj : j ∈ Ring.jacobson A) : IsUnit (1 + j) := by
  rw [← Ideal.jacobson_bot] at hj
  have hleft : ∀ j' ∈ Ideal.jacobson (⊥ : Ideal A), ∃ z, z * (1 + j') = 1 := by
    intro j' hj'
    obtain ⟨z, hz⟩ := (Ideal.mem_jacobson_iff.mp hj') 1
    rw [Ideal.mem_bot, mul_one] at hz
    refine ⟨z, ?_⟩
    rw [mul_add, mul_one, add_comm]
    exact sub_eq_zero.mp hz
  obtain ⟨z, hz⟩ := hleft j hj
  have hzj : -(z * j) ∈ Ideal.jacobson (⊥ : Ideal A) :=
    Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hj)
  have hzeq : (1 : A) + -(z * j) = z := by
    have h1 : z + z * j = 1 := by rw [← hz, mul_add, mul_one]
    rw [← h1]; abel
  obtain ⟨w, hw⟩ := hleft _ hzj
  rw [hzeq] at hw
  have hwz : w = 1 + j := by
    calc w = w * (z * (1 + j)) := by rw [hz, mul_one]
      _ = w * z * (1 + j) := by rw [mul_assoc]
      _ = 1 + j := by rw [hw, one_mul]
  exact ⟨⟨1 + j, z, by rw [← hwz]; exact hw, hz⟩, rfl⟩

/-- **The core of Navarro (5.4).**  If `x` lies in the corner `fAf` and `u = x + (1 - f)` is a
unit of `A`, then `f u⁻¹ f` is a two-sided inverse of `x` in that corner.  No ring structure on
the corner is needed. -/
theorem exists_corner_inverse_of_isUnit {A : Type*} [Ring A] {f x : A} (hf : IsIdempotentElem f)
    (hx : x = f * x * f) (hunit : IsUnit (x + (1 - f))) :
    ∃ y : A, y = f * y * f ∧ x * y = f ∧ y * x = f := by
  have hff : f * f = f := hf
  set u : A := x + (1 - f) with hu
  obtain ⟨U, hU⟩ := hunit
  set v : A := ((U⁻¹ : Aˣ) : A) with hv
  have huv : u * v = 1 := by rw [hv, ← hU]; exact U.mul_inv
  have hvu : v * u = 1 := by rw [hv, ← hU]; exact U.inv_mul
  have hfx : f * x = x := by rw [hx, ← mul_assoc, ← mul_assoc, hff]
  have hxfe : x * f = x := by
    conv_lhs => rw [hx]
    rw [mul_assoc, hff, ← hx]
  have hfu : f * u = x := by rw [hu, mul_add, hfx, mul_sub, mul_one, hff, sub_self, add_zero]
  have huf : u * f = x := by rw [hu, add_mul, hxfe, sub_mul, one_mul, hff, sub_self, add_zero]
  refine ⟨f * v * f, ?_, ?_, ?_⟩
  · rw [mul_assoc f (f * v * f) f, mul_assoc (f * v) f f, hff, ← mul_assoc f (f * v) f,
      ← mul_assoc f f v, hff]
  · calc x * (f * v * f) = x * v * f := by rw [← mul_assoc, ← mul_assoc, hxfe]
      _ = f * u * v * f := by rw [hfu]
      _ = f := by rw [mul_assoc f u v, huv, mul_one, hff]
  · calc f * v * f * x = f * v * x := by rw [mul_assoc, hfx]
      _ = f * v * (u * f) := by rw [huf]
      _ = f := by rw [mul_assoc, ← mul_assoc v u f, hvu, one_mul, hff]

/-- **The characteristic-`p` variant.**  If `x - f` is nilpotent then `u = x + (1 - f)` is a unit,
so `x` is again invertible in the corner.  This is what Navarro (5.5) uses in `Z(FG)`, where
`e_B x - e_B` is nilpotent because every block character kills it. -/
theorem exists_corner_inverse_of_isNilpotent {A : Type*} [Ring A] {f x : A}
    (hf : IsIdempotentElem f) (hx : x = f * x * f) (hnil : IsNilpotent (x - f)) :
    ∃ y : A, y = f * y * f ∧ x * y = f ∧ y * x = f := by
  refine exists_corner_inverse_of_isUnit hf hx ?_
  have hrw : x + (1 - f) = 1 + (x - f) := by abel
  rw [hrw]
  exact hnil.isUnit_one_add

variable {𝒪 A : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [Ring A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
  [Nontrivial A]

/-- `𝔪·A` sits inside the Jacobson radical — Navarro (5.3), in ideal form. -/
theorem map_maximalIdeal_le_ringJacobson :
    (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A) ≤ Ring.jacobson A := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  exact algebraMap_maximalIdeal_mem_ringJacobson ha

/-- **Navarro (5.4).**  An element of the corner `fAf` congruent to `f` modulo `𝔪·A` has a
two-sided inverse in that corner. -/
theorem exists_corner_inverse {f x : A} (hf : IsIdempotentElem f) (hx : x = f * x * f)
    (hxf : f - x ∈ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    ∃ y : A, y = f * y * f ∧ x * y = f ∧ y * x = f := by
  refine exists_corner_inverse_of_isUnit hf hx ?_
  have hrw : x + (1 - f) = 1 + (x - f) := by abel
  rw [hrw]
  refine isUnit_one_add_of_mem_ringJacobson ?_
  have hneg : x - f = -(f - x) := by abel
  rw [hneg]
  exact Submodule.neg_mem _ (map_maximalIdeal_le_ringJacobson (𝒪 := 𝒪) hxf)

end OddOrder
