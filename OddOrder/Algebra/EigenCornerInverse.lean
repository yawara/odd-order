/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.CornerInverse

/-!
# Navarro (5.7): the eigenvector acts injectively

The last step of Navarro's proof of (5.7) is that multiplication by `s` is injective on
`V = M f_b`.  Written for a left module — which is what a `Representation` gives, and which is
legitimate here because `f_b` commutes with `h` — the argument is:

* `f = (1 - f_B) f_b` is an idempotent, because `f_B` is central;
* `x = (1 - f_B) s` satisfies `f x f = x`, because `f_b s f_b = s`;
* `f - x = (1 - f_B)(f_b - s)`, and `f_b - s = (f_b - w) + (w - s)`, where the first summand is
  killed by `1 - f_B` (Navarro (5.6.a)) and the second lies in `𝔪·𝒪G` (because `s* = w*`);
* so (5.4) gives `y` with `y x = f`;
* and for `v` in the module with `f_b v = v` and `f_B v = 0` — the latter is (3.13.a) —
  `v = f v = y x v = y (1 - f_B) (s v)`, which vanishes as soon as `s v` does.

## Main results

* `OddOrder.exists_corner_inverse_eigen` — the corner inverse of `(1 - c) s`
* `OddOrder.eq_zero_of_apply_eq_zero_of_corner_inverse` — injectivity on the module
-/

namespace OddOrder

section CornerInverse

variable {𝒪 A : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [Ring A] [Algebra 𝒪 A]
  [Module.Finite 𝒪 A] [Nontrivial A]

/-- **Navarro (5.7), the corner inverse.**  With `c` a central idempotent, `e` an idempotent,
`(1 - c) e = (1 - c) w`, `s ≡ w` modulo `𝔪`, and `e s e = s`, the element `(1 - c) s` is
invertible in the corner ring of `f = (1 - c) e`. -/
theorem exists_corner_inverse_eigen {c e w s : A} (hc : IsIdempotentElem c)
    (hccent : ∀ a : A, Commute c a) (he : IsIdempotentElem e)
    (hcew : (1 - c) * e = (1 - c) * w)
    (hsw : s - w ∈ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))
    (hes : e * s * e = s) :
    ∃ y : A, y * ((1 - c) * s) = (1 - c) * e ∧ ((1 - c) * s) * y = (1 - c) * e := by
  have hcc : c * c = c := hc
  have hc' : (1 - c) * (1 - c) = 1 - c := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hcc, sub_self, sub_zero]
  have hcom : ∀ a : A, (1 - c) * a = a * (1 - c) := fun a => by
    rw [sub_mul, one_mul, mul_sub, mul_one, (hccent a).eq]
  -- multiplying two `(1 - c)`-multiples collapses the central factor
  have hstep : ∀ a b : A, ((1 - c) * a) * ((1 - c) * b) = (1 - c) * (a * b) := by
    intro a b
    rw [mul_assoc, ← mul_assoc a (1 - c) b, ← hcom a, mul_assoc (1 - c) a b, ← mul_assoc, hc']
  have hf : IsIdempotentElem ((1 - c) * e) := by
    change ((1 - c) * e) * ((1 - c) * e) = (1 - c) * e
    rw [hstep, he.eq]
  have hx : (1 - c) * s = ((1 - c) * e) * ((1 - c) * s) * ((1 - c) * e) := by
    rw [hstep, hstep, hes]
  have hxf : ((1 - c) * e) - (1 - c) * s
      ∈ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A) := by
    have hsplit : ((1 - c) * e) - (1 - c) * s = -((1 - c) * (s - w)) := by
      rw [mul_sub, hcew]
      abel
    rw [hsplit]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hsw)
  obtain ⟨y, -, hxy, hyx⟩ := exists_corner_inverse hf hx hxf
  exact ⟨y, hyx, hxy⟩

end CornerInverse

section Module

variable {A : Type*} [Ring A] {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-- **Navarro (5.7), injectivity on the module.**  If `y (1 - c) s = (1 - c) e` and `v` satisfies
`e v = v`, `c v = 0`, then `s v = 0` forces `v = 0`.

Phrased through a representation `ρ : A →+* Module.End K M` rather than a `Module A M` instance,
because the module in Navarro (5.7) is a `K`-space on which `𝒪G` acts through `KG`. -/
theorem eq_zero_of_apply_eq_zero_of_corner_inverse (ρ : A →+* Module.End K M) {c e s y : A}
    (hy : y * ((1 - c) * s) = (1 - c) * e)
    {v : M} (hve : ρ e v = v) (hvc : ρ c v = 0) (hsv : ρ s v = 0) : v = 0 := by
  have hone : ρ (1 - c) v = v := by
    rw [map_sub, map_one]
    change v - ρ c v = v
    rw [hvc, sub_zero]
  have h1 : ρ ((1 - c) * e) v = v := by rw [map_mul]; change ρ (1 - c) (ρ e v) = v; rw [hve, hone]
  have h2 : ρ ((1 - c) * e) v = 0 := by
    rw [← hy, map_mul, map_mul]
    change ρ y (ρ (1 - c) (ρ s v)) = 0
    rw [hsv, map_zero, map_zero]
  rw [← h1, h2]

end Module

end OddOrder
