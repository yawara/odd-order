/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroup
import OddOrder.Algebra.QuadraticTraceCorrection
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.QuadraticExtensions

/-!
# Twisted-product coordinates on the Hermitian root group

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3, pp. 130–131.

`RootGroup n` carries the book's coordinates: pairs `(a, b)` of elements of `E = GF(q²)`
with `b + b̄ = a ā`, multiplying by `(a,b)(c,d) = (a+c, b+d+a c̄)`.  Chapter III §3 instead
models the same group as a `BilinearTwistedProduct`, whose second coordinate ranges over
the *subfield* `F` freely.  Chapter IV §3 (4) is stated in the first presentation and
proved from facts established in the second, so the two must be matched.

The matching is **not** the naive change of coordinates.  Writing `b = b₀(a) + z` for a
section `b₀` of the trace leaves a cocycle
`b₀(a) + b₀(c) + b₀(a+c) + a c̄`, which is not bi-additive: `b₀` cannot be chosen additive,
since `Tr ∘ b₀` is the norm and the norm is not additive.

What works is to correct by the norm itself.  Fixing `u` with `Tr u = 1` and setting

  `Ξ (a, b) = (a, b + u a ā)`,

the second coordinate lands in `F` (`snd_add_norm_mem`) because `Tr b = a ā` is exactly what
the root-group condition says, and the failure of `a ↦ u a ā` to be additive is *precisely*
the trace term `u · Tr(a c̄)` needed to convert the cocycle `a c̄` into an `F`-valued one
(`norm_cocycle`).  Those two facts are this file; the bundled isomorphism is assembled from
them.

## Main results

* `ProjectiveUnitary.frobTrace_eq_add_star` — the relative trace is `z ↦ z + z̄`.
* `ProjectiveUnitary.norm_mem_frobFixed` — `a ā` lies in `F`.
* `ProjectiveUnitary.snd_add_norm_mem` — `b + u a ā` lies in `F`, for `x = (a,b)` in the
  root group.
* `ProjectiveUnitary.norm_cocycle` — the coboundary of `a ↦ u a ā` is `u · Tr(a c̄)`.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

open OddOrder.FiniteField

variable {n : ℕ}

/-- Characteristic two, in the form the computations below consume. -/
theorem two_eq_zero_field (n : ℕ) : (2 : Field n) = 0 := by
  have h := CharTwo.add_self_eq_zero (1 : Field n)
  linear_combination h

/-- **The relative trace of `E / F` is `z ↦ z + z̄`.**  This is the bridge between the
`star` of the unitary coordinates and the `frobTrace` of the quadratic-extension API:
`star` is the `q`-power map (`conjugation_apply`). -/
theorem frobTrace_eq_add_star (hn : 0 < n) (z : Field n) :
    frobTrace (E := Field n) n z = z + star z := by
  rw [frobTrace_apply, star_eq_conjugation, conjugation_apply n hn]

/-- **The Hermitian norm lands in `F`.**  `Tr(a ā) = a ā + ā a = 0` in characteristic
two. -/
theorem norm_mem_frobFixed (hn : 0 < n) (a : Field n) :
    a * star a ∈ frobFixedSubfield (Field n) 2 n := by
  rw [← frobTrace_eq_zero_iff, frobTrace_eq_add_star hn, star_mul, star_star]
  exact CharTwo.add_self_eq_zero _

/-- **The corrected second coordinate lands in `F`.**

For `x = (a, b)` in the root group, `Tr b = a ā` *is* the defining condition, and
`Tr (u a ā) = a ā · Tr u = a ā` because the norm lies in `F` and `Tr u = 1`; the two cancel
in characteristic two. -/
theorem snd_add_norm_mem (hn : 0 < n) {u : Field n}
    (hu : frobTrace (E := Field n) n u = 1) (x : RootGroup n) :
    x.snd + u * (x.fst * star x.fst) ∈ frobFixedSubfield (Field n) 2 n := by
  rw [← frobTrace_eq_zero_iff, map_add]
  -- `Tr b = a ā`, by the root-group condition
  have hb : frobTrace (E := Field n) n x.snd = x.fst * star x.fst := by
    rw [frobTrace_eq_add_star hn]
    exact x.condition
  -- `Tr (u a ā) = a ā`
  have hcorr : frobTrace (E := Field n) n (u * (x.fst * star x.fst))
      = x.fst * star x.fst := by
    rw [mul_comm u (x.fst * star x.fst),
      frobTrace_mul_of_mem n (norm_mem_frobFixed hn x.fst) u, hu, mul_one]
  rw [hb, hcorr]
  exact CharTwo.add_self_eq_zero _

/-- **The coboundary of `a ↦ u a ā` is the trace term.**

This is what makes the correction work: expanding `(a+c)(ā+c̄)` leaves exactly
`a c̄ + c ā`, which is `Tr (a c̄)`.  So subtracting `u a ā` from the second coordinate turns
the `E`-valued cocycle `a c̄` of the root group into the `F`-valued one
`a c̄ + u · Tr(a c̄)` of the twisted product. -/
theorem norm_cocycle (hn : 0 < n) (u a c : Field n) :
    u * (a * star a) + u * (c * star c) + u * ((a + c) * star (a + c))
      = u * frobTrace (E := Field n) n (a * star c) := by
  have h2 : (2 : Field n) = 0 := two_eq_zero_field n
  rw [frobTrace_eq_add_star hn, star_add, star_mul, star_star]
  linear_combination (u * (a * star a) + u * (c * star c)) * h2

/-! ## The corrected cocycle -/

/-- The Hermitian cocycle `(x, y) ↦ x ȳ` of the root group, as a `ZMod 2`-bilinear map.
It is bi-additive because `star` is the `q`-power map. -/
noncomputable def hermitianBilin (n : ℕ) :
    LinearMap.BilinMap (ZMod 2) (Field n) (Field n) where
  toFun x :=
    { toFun := fun y => x * star y
      map_add' := fun y y' => by rw [star_add, mul_add]
      map_smul' := fun c y => by
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;> simp }
  map_add' x x' := LinearMap.ext fun y => by simp [add_mul]
  map_smul' c x := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with hc | hc <;> subst hc <;>
      exact LinearMap.ext fun y => by simp

@[simp] theorem hermitianBilin_apply (n : ℕ) (x y : Field n) :
    hermitianBilin n x y = x * star y := rfl

/-- The trace correction of the Hermitian cocycle: `x ȳ + u · Tr(x ȳ)`.  It has the same
diagonal as `hermitianBilin` and, when `Tr u = 1`, takes values in `F`. -/
noncomputable def correctedBilin (n : ℕ) (u : Field n) :
    LinearMap.BilinMap (ZMod 2) (Field n) (Field n) :=
  hermitianBilin n + u • (hermitianBilin n).compr₂ (frobTrace (E := Field n) n)

@[simp] theorem correctedBilin_apply (n : ℕ) (u x y : Field n) :
    correctedBilin n u x y = x * star y + u * frobTrace (E := Field n) n (x * star y) := by
  simp only [correctedBilin, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.compr₂_apply, hermitianBilin_apply, smul_eq_mul]

/-- **The corrected cocycle is `F`-valued**, when `Tr u = 1`: the trace of `u · Tr z` is
`Tr z · Tr u = Tr z`, which cancels `Tr z` in characteristic two. -/
theorem correctedBilin_mem (hn : 0 < n) {u : Field n}
    (hu : frobTrace (E := Field n) n u = 1) (x y : Field n) :
    correctedBilin n u x y ∈ frobFixedSubfield (Field n) 2 n := by
  have hcard : Nat.card (Field n) = (2 ^ n) ^ 2 := by
    rw [natCard_field n hn, ← pow_mul]
    congr 1
    omega
  rw [← frobTrace_eq_zero_iff, correctedBilin_apply, map_add,
    mul_comm u (frobTrace (E := Field n) n (x * star y)),
    frobTrace_mul_of_mem n (frobTrace_mem n hcard (x * star y)) u, hu, mul_one]
  exact CharTwo.add_self_eq_zero _

/-- The corrected cocycle as an `F`-valued bilinear map — the shape
`BilinearTwistedProduct` consumes. -/
noncomputable def rootBilin (hn : 0 < n) {u : Field n}
    (hu : frobTrace (E := Field n) n u = 1) :
    LinearMap.BilinMap (ZMod 2) (Field n) ↥(frobFixedSubfield (Field n) 2 n) :=
  bilinCodRestrict n (correctedBilin n u) (correctedBilin_mem hn hu)

@[simp] theorem rootBilin_apply_coe (hn : 0 < n) {u : Field n}
    (hu : frobTrace (E := Field n) n u = 1) (x y : Field n) :
    ((rootBilin hn hu x y : ↥(frobFixedSubfield (Field n) 2 n)) : Field n)
      = x * star y + u * frobTrace (E := Field n) n (x * star y) := by
  rw [rootBilin]
  change correctedBilin n u x y = _
  rw [correctedBilin_apply]

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
