/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.CenterFieldExponent

/-!
# The centre coordinate `Q₀ ≃ F`, at the level of `G`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, p. 125.

`exists_center_coordinate_equiv` gives the centre coordinate as an additive isomorphism
`ι : Additive Z(Q) ≃+ F` together with the exponent `d` describing the `K`-action.  Every
statement of Ch. IV §2, however, is about elements of `G` lying in `Q₀` — `s`, `y`, `s^a`.
This file bridges the two: `centerCoord` reads off the `E`-coordinate of an element of
`Q₀` directly, and is additive, with `0` only at `1`.

That is what turns step (10)'s group-theoretic hypothesis `y · s^{a⁻¹} = s^b` into the
book's coordinate form `b^{1+θ} = α + a^{-(1+θ)}`.

## Main results

* `Hypothesis.toCenter` — an element of `Q₀` as an element of `Z(Q)`, using
  `LemmaFiveSetup.centerEqQ0`.
* `Hypothesis.centerCoord` — its `E`-coordinate.
* `Hypothesis.centerCoord_mul`, `Hypothesis.centerCoord_eq_zero_iff` — additivity, and
  that the coordinate vanishes exactly at `1`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G] (hyp : Hypothesis G Ω)

include hyp

/-- An element of `Q₀`, viewed inside `Z(Q)`.

`LemmaFiveSetup.centerEqQ0` is what identifies the two; `Q₀` is the group Ch. IV §2 talks
about, `Z(Q)` the one the coordinate `ι` is defined on. -/
def toCenter {m : ℕ} (s : hyp.LemmaFiveSetup m) {x : G} (hx : x ∈ hyp.Q0) :
    ↥(Subgroup.center hyp.Q) :=
  ⟨⟨x, hyp.Q0_le_Q hx⟩, by rw [s.centerEqQ0]; exact hx⟩

@[simp] theorem toCenter_coe {m : ℕ} (s : hyp.LemmaFiveSetup m) {x : G}
    (hx : x ∈ hyp.Q0) :
    (((hyp.toCenter s hx : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) : G) = x := rfl

theorem toCenter_mul {m : ℕ} (s : hyp.LemmaFiveSetup m) {x y : G} (hx : x ∈ hyp.Q0)
    (hy : y ∈ hyp.Q0) :
    hyp.toCenter s (hyp.Q0.mul_mem hx hy)
      = hyp.toCenter s hx * hyp.toCenter s hy :=
  Subtype.ext (Subtype.ext rfl)

theorem toCenter_eq_one_iff {m : ℕ} (s : hyp.LemmaFiveSetup m) {x : G}
    (hx : x ∈ hyp.Q0) : hyp.toCenter s hx = 1 ↔ x = 1 := by
  constructor
  · intro h
    exact congrArg (fun z : ↥(Subgroup.center hyp.Q) => ((z : ↥hyp.Q) : G)) h
  · rintro rfl
    exact Subtype.ext (Subtype.ext rfl)

/-- **The `E`-coordinate of an element of `Q₀`** (Peterfalvi Part II, p. 125): the book's
`(0, c)`, read off through the centre coordinate `ι` of `exists_center_coordinate_equiv`.
-/
noncomputable def centerCoord {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {x : G} (hx : x ∈ hyp.Q0) : M.E :=
  ((ι (Additive.ofMul (hyp.toCenter s hx)) :
    ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)

/-- The coordinate is additive: `Q₀` is elementary abelian and `ι` is an additive
isomorphism, so multiplying in `Q₀` adds coordinates. -/
theorem centerCoord_mul {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {x y : G} (hx : x ∈ hyp.Q0) (hy : y ∈ hyp.Q0) :
    hyp.centerCoord s M ι (hyp.Q0.mul_mem hx hy)
      = hyp.centerCoord s M ι hx + hyp.centerCoord s M ι hy := by
  simp only [centerCoord, hyp.toCenter_mul s hx hy, ofMul_mul, map_add]
  push_cast
  ring

/-- The coordinate vanishes exactly at `1`.

This is what makes `y · s^{a⁻¹} ≠ 1` — the existence condition for step (10)'s `b`, and
the book's stopping rule `u_i ≠ α` — a statement about coordinates. -/
theorem centerCoord_eq_zero_iff {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {x : G} (hx : x ∈ hyp.Q0) :
    hyp.centerCoord s M ι hx = 0 ↔ x = 1 := by
  rw [← hyp.toCenter_eq_one_iff s hx]
  constructor
  · intro h
    have hz : (ι (Additive.ofMul (hyp.toCenter s hx)) :
        ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) = 0 := Subtype.ext h
    have := (AddEquiv.map_eq_zero_iff ι).mp hz
    exact this
  · intro h
    simp only [centerCoord, h]
    change ((ι 0 : ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E) = 0
    rw [map_zero]
    rfl

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
