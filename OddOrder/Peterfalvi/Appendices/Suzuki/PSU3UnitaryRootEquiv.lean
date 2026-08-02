/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.StandardGenerators
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.UnitaryCoordinates

/-!
# The unitary coordinates *are* the root group of `PSU(3, q)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §3 (4)–(5), pp. 130–131.

`unitaryCoord` presents a Hermitian twisted product as the group of pairs `(a, y)` with
`Tr y = a ā` and multiplication `(a, y)(c, w) = (a + c, y + w + a c̄)`, which is the
definition of `RootGroup q`.  This file turns that observation into an isomorphism, along
any identification `σ : E ≃+* GF(q²)` of the two coefficient fields.

The point is that the isomorphism is built *out of the coordinates*, so both of them are
computable through it:

  `(unitaryRootEquiv σ p).fst = σ p.quotient`,  `(unitaryRootEquiv σ p).snd = σ (y p)`.

That is what `nonempty_mulEquiv_rootGroup` — which only produces an abstract isomorphism,
through a diagonal-matching argument that leaves the central coordinate free — cannot
supply, and it is exactly what the comparison of §3's formula for `f` with the standard
model's reciprocal needs: both are formulas in `(a, y)`.

## Main results

* `unitaryRootEquiv` — the coordinate isomorphism, with `unitaryRootEquiv_fst` and
  `unitaryRootEquiv_snd`.
* `unitaryRootEquiv_symm_apply` — its inverse, through `ofUnitary`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.FiniteField
open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

section /- Ch. IV §3 (4): the two presentations of `Q` (pp. 130–131) -/

variable {E : Type*} [_root_.Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E] {m : ℕ}

omit [Finite E] [CharP E 2] [Algebra (ZMod 2) E] in
/-- Conjugation on `GF(q²)` is the `q`-power map, transported along a field
isomorphism. -/
theorem star_ringEquiv_apply (hm : 0 < m) (σ : E ≃+* Field m) (x : E) :
    star (σ x) = σ (x ^ 2 ^ m) := by
  rw [star_eq_conjugation, conjugation_apply m hm,
    map_pow]

/-- The root-group relation `y + ȳ = a ā` holds of the unitary coordinates, transported
along `σ`; this is `unitaryCoord_frobTrace`. -/
theorem unitaryCoord_condition (hm : 0 < m) (hcard : Nat.card E = (2 ^ m) ^ 2) {u : E}
    (hu : frobTrace (E := E) m u = 1)
    (σ : E ≃+* Field m)
    (p : BilinearTwistedProduct (hermitianCocycle m hcard hu)) :
    σ (unitaryCoord m u p) + star (σ (unitaryCoord m u p))
      = σ p.quotient * star (σ p.quotient) := by
  rw [star_ringEquiv_apply hm, star_ringEquiv_apply hm, ← map_add, ← map_mul]
  exact congrArg σ (by
    simpa only [frobTrace_apply] using unitaryCoord_frobTrace m hcard hu p)

/-- **The unitary coordinates identify a Hermitian twisted product with `RootGroup q`**
(Peterfalvi Part II, Ch. IV §3 (4), p. 131).

The map is literally "read off the two coordinates and push them through `σ`":
`unitaryCoord_mul` is the multiplication rule of `RootGroup`, `unitaryCoord_frobTrace` is
its defining relation, and `eq_of_unitaryCoord_eq` together with `ofUnitary` makes it a
bijection. -/
noncomputable def unitaryRootEquiv (hm : 0 < m) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {u : E} (hu : frobTrace (E := E) m u = 1)
    (σ : E ≃+* Field m) :
    BilinearTwistedProduct (hermitianCocycle m hcard hu) ≃* RootGroup m where
  toFun p :=
    { fst := σ p.quotient
      snd := σ (unitaryCoord m u p)
      condition := unitaryCoord_condition hm hcard hu σ p }
  invFun x :=
    ofUnitary m hcard hu (σ.symm x.fst) (σ.symm x.snd) (by
      have hx := x.condition
      rw [star_eq_conjugation, star_eq_conjugation,
        conjugation_apply m hm,
        conjugation_apply m hm] at hx
      have := congrArg σ.symm hx
      rw [map_add, map_mul, map_pow, map_pow] at this
      simpa only [frobTrace_apply] using this)
  left_inv p := by
    refine eq_of_unitaryCoord_eq (u := u) m ?_ ?_
    · rw [ofUnitary_quotient, σ.symm_apply_apply]
    · rw [ofUnitary_unitaryCoord, σ.symm_apply_apply]
  right_inv x := by
    refine RootGroup.ext ?_ ?_
    · change σ (ofUnitary m hcard hu _ _ _).quotient = x.fst
      rw [ofUnitary_quotient, σ.apply_symm_apply]
    · change σ (unitaryCoord m u (ofUnitary m hcard hu _ _ _)) = x.snd
      rw [ofUnitary_unitaryCoord, σ.apply_symm_apply]
  map_mul' p q := by
    refine RootGroup.ext ?_ ?_
    · change σ (p * q).quotient = σ p.quotient + σ q.quotient
      exact map_add σ _ _
    · change σ (unitaryCoord m u (p * q))
        = σ (unitaryCoord m u p) + σ (unitaryCoord m u q)
          + σ p.quotient * star (σ q.quotient)
      rw [unitaryCoord_mul m hcard hu, star_ringEquiv_apply hm, map_add, map_add, map_mul]

@[simp] theorem unitaryRootEquiv_fst (hm : 0 < m) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {u : E} (hu : frobTrace (E := E) m u = 1)
    (σ : E ≃+* Field m)
    (p : BilinearTwistedProduct (hermitianCocycle m hcard hu)) :
    (unitaryRootEquiv hm hcard hu σ p).fst = σ p.quotient := rfl

@[simp] theorem unitaryRootEquiv_snd (hm : 0 < m) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {u : E} (hu : frobTrace (E := E) m u = 1)
    (σ : E ≃+* Field m)
    (p : BilinearTwistedProduct (hermitianCocycle m hcard hu)) :
    (unitaryRootEquiv hm hcard hu σ p).snd = σ (unitaryCoord m u p) := rfl

theorem unitaryRootEquiv_symm_apply (hm : 0 < m) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {u : E} (hu : frobTrace (E := E) m u = 1)
    (σ : E ≃+* Field m) (x : RootGroup m) :
    ((unitaryRootEquiv hm hcard hu σ).symm x).quotient = σ.symm x.fst := rfl

/-- **The reciprocal of §3 (4) in the two presentations.**

`RootGroup.reciprocal` is `(a, y) ↦ (a/y, 1/y)`; stated through the coordinates of the
source, that is exactly the formula stages (4)–(5) prove for `f`.  So a value satisfying
those two equations is carried by `unitaryRootEquiv` to the reciprocal of the image. -/
theorem unitaryRootEquiv_reciprocal (hm : 0 < m) (hcard : Nat.card E = (2 ^ m) ^ 2)
    {u : E} (hu : frobTrace (E := E) m u = 1)
    (σ : E ≃+* Field m)
    {p p' : BilinearTwistedProduct (hermitianCocycle m hcard hu)}
    (hq : p'.quotient = p.quotient / unitaryCoord m u p)
    (hy : unitaryCoord m u p' = (unitaryCoord m u p)⁻¹)
    (h1 : unitaryRootEquiv hm hcard hu σ p ≠ 1) :
    unitaryRootEquiv hm hcard hu σ p'
      = RootGroup.reciprocal (unitaryRootEquiv hm hcard hu σ p) h1 := by
  refine RootGroup.ext ?_ ?_
  · rw [unitaryRootEquiv_fst, RootGroup.reciprocal_fst, unitaryRootEquiv_fst,
      unitaryRootEquiv_snd, hq, map_div₀]
  · rw [unitaryRootEquiv_snd, RootGroup.reciprocal_snd, unitaryRootEquiv_snd, hy,
      map_inv₀, one_div]

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
