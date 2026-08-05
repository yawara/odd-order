/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.VirtualCharacter

/-!
# The character pairing and its integrality on virtual characters

The `K`-bilinear form `(a, b)_G = (1/|G|) ∑_{g ∈ G} a(g⁻¹) b(g)` on functions `G → K`.  Over `ℂ`
this is the usual Hermitian product read through `χ(g⁻¹) = conj χ(g)`; over an arbitrary field of
characteristic zero the bilinear shape is the right one, and it is all Brauer's argument needs.

The point of this file is the **integrality**: the pairing of the characters of two
finite-dimensional representations is the dimension of the space of intertwiners
(`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`), hence a natural number, and by
bilinearity the pairing of two virtual characters is a rational integer.  No splitting field and
no orthonormal basis is involved — that is what lets the whole Brauer–Tate argument avoid
equipping every elementary subgroup with a Wedderburn splitting.

## Main definitions

* `OddOrder.RepresentationTheory.charPairing` — Gorenstein's `(a, b)_G`

## Main results

* `OddOrder.RepresentationTheory.charPairing_isRepCharacter` — `(χ_V, χ_W)_G = dim Hom_{KG}(V, W)`
* `OddOrder.RepresentationTheory.charPairing_mem_intRange` — the pairing of two virtual characters
  is a rational integer

## References

* D. Gorenstein, *Finite Groups*, §4.7 (`references/gorenstein/pages/gorenstein-p16*.png`).
-/

namespace OddOrder.RepresentationTheory

open Module

variable {K G : Type*} [Field K] [Group G] [Fintype G]

/-- **The character pairing** `(a, b)_G = (1/|G|) ∑_{g ∈ G} a(g⁻¹) b(g)`.  Bilinear (not
sesquilinear): over a general field there is no complex conjugation, and `g ↦ g⁻¹` plays its
role. -/
noncomputable def charPairing (K : Type*) [Field K] {G : Type*} [Group G] [Fintype G]
    (a b : G → K) : K :=
  (Nat.card G : K)⁻¹ * ∑ g : G, a g⁻¹ * b g

theorem charPairing_add_left (a a' b : G → K) :
    charPairing K (a + a') b = charPairing K a b + charPairing K a' b := by
  simp only [charPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem charPairing_add_right (a b b' : G → K) :
    charPairing K a (b + b') = charPairing K a b + charPairing K a b' := by
  simp only [charPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem charPairing_neg_left (a b : G → K) :
    charPairing K (-a) b = -charPairing K a b := by
  simp only [charPairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]

theorem charPairing_neg_right (a b : G → K) :
    charPairing K a (-b) = -charPairing K a b := by
  simp only [charPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

@[simp]
theorem charPairing_zero_left (b : G → K) : charPairing K (0 : G → K) b = 0 := by
  simp [charPairing]

@[simp]
theorem charPairing_zero_right (a : G → K) : charPairing K a (0 : G → K) = 0 := by
  simp [charPairing]

/-! ### Integrality -/

/-- **The pairing of two genuine characters is the dimension of the intertwiner space.**  This is
`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`; in particular the value is a natural
number, with no orthonormality and no splitting field in sight. -/
theorem charPairing_isRepCharacter [CharZero K] {a b : G → K} (ha : IsRepCharacter K a)
    (hb : IsRepCharacter K b) : ∃ n : ℕ, charPairing K a b = (n : K) := by
  obtain ⟨n, ρ, rfl⟩ := ha
  obtain ⟨m, σ, rfl⟩ := hb
  haveI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine ⟨finrank K (Representation.IntertwiningMap ρ σ), ?_⟩
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ, charPairing]
  exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)

/-- **The pairing of two virtual characters is a rational integer.**  Bilinearity plus the
previous result. -/
theorem charPairing_mem_intRange [CharZero K] {a b : G → K}
    (ha : a ∈ virtualCharacters K G) (hb : b ∈ virtualCharacters K G) :
    charPairing K a b ∈ (Int.castRingHom K).range := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
      induction hb using AddSubgroup.closure_induction with
      | mem b hb =>
          obtain ⟨n, hn⟩ := charPairing_isRepCharacter ha hb
          exact ⟨(n : ℤ), by simp [hn]⟩
      | zero => simp
      | add x y _ _ hx hy => simpa only [charPairing_add_right] using
          (Int.castRingHom K).range.add_mem hx hy
      | neg x _ hx => simpa only [charPairing_neg_right] using
          (Int.castRingHom K).range.neg_mem hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [charPairing_add_left] using
      (Int.castRingHom K).range.add_mem hx hy
  | neg x _ hx => simpa only [charPairing_neg_left] using (Int.castRingHom K).range.neg_mem hx

end OddOrder.RepresentationTheory
