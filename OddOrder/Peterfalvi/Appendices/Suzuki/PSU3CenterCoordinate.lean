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

/-- The coordinate is injective, `ι` and `toCenter` both being injective.  So an equation
between elements of `Q₀` is equivalent to the corresponding equation of coordinates —
which is how the group-theoretic form of step (10) and the book's coordinate form are
the same statement. -/
theorem centerCoord_injective {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {x y : G} (hx : x ∈ hyp.Q0) (hy : y ∈ hyp.Q0)
    (h : hyp.centerCoord s M ι hx = hyp.centerCoord s M ι hy) : x = y := by
  have h1 : (ι (Additive.ofMul (hyp.toCenter s hx)) :
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
      = ι (Additive.ofMul (hyp.toCenter s hy)) := Subtype.ext h
  have h3 : hyp.toCenter s hx = hyp.toCenter s hy := ι.injective h1
  calc x = (((hyp.toCenter s hx : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) : G) := rfl
    _ = (((hyp.toCenter s hy : ↥(Subgroup.center hyp.Q)) : ↥hyp.Q) : G) := by rw [h3]
    _ = y := rfl

/-- **An equation in `Q₀` is exactly the corresponding equation of coordinates.**

With `centerCoord_mul` and `centerCoord_conj` this reduces any identity among products
and `K`-conjugates in `Q₀` — step (10)'s `y · s^{a⁻¹} = s^b`, say — to arithmetic in `E`,
which is the book's coordinate form `b^{1+θ} = α + a^{-(1+θ)}`. -/
theorem eq_iff_centerCoord_eq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m))
    {x y : G} (hx : x ∈ hyp.Q0) (hy : y ∈ hyp.Q0) :
    x = y ↔ hyp.centerCoord s M ι hx = hyp.centerCoord s M ι hy := by
  constructor
  · rintro rfl
    rfl
  · exact hyp.centerCoord_injective s M ι hx hy

/-! ## The `K`-action in coordinates

`K` acts on `Q₀` by conjugation; `exists_center_coordinate_equiv` says that in
coordinates this is multiplication by `μ(k)^d`.  The book writes that action as
`c^x = x^{1+θ} c` (Ch. III §3, p. 119) — on `F^×` the map `x ↦ x^{1+θ}` *is* an integer
power, which is why a single exponent `d` suffices.
-/

/-- `a ∈ K` as an element of the actual `K`-actor `conjQByK.range`. -/
def kActor {a : G} (ha : a ∈ hyp.K) : ↥hyp.actualKActor :=
  ⟨hyp.conjQByK ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩

/-- `kActor` sends the identity to the identity — `conjQByK` is a homomorphism.

Step (15) uses this to transport `κ = 1` (from `K ∩ W = 1`) across `μ`: the scalar
`μ(κ)` is then `1`, which is what forces `c_{m₁} = α`. -/
@[simp] theorem kActor_one (h : (1 : G) ∈ hyp.K) : hyp.kActor h = 1 := by
  apply Subtype.ext
  change hyp.conjQByK ⟨1, h⟩ = 1
  rw [show (⟨1, h⟩ : ↥hyp.K) = 1 from Subtype.ext rfl, map_one]

/-- `kActor` turns inverses into inverses — `conjQByK` is a homomorphism.

The hypothesis is stated as an equation rather than by `inv_mem` so that a caller may
present the element in whatever shape it arises in: §3 (3) meets it as `(a⁻¹)²`, which is
`(a²)⁻¹` only up to `inv_pow`. -/
theorem kActor_eq_inv {a b : G} (ha : a ∈ hyp.K) (hb : b ∈ hyp.K) (hab : b = a⁻¹) :
    hyp.kActor hb = (hyp.kActor ha)⁻¹ := by
  apply Subtype.ext
  change hyp.conjQByK ⟨b, hb⟩ = (hyp.conjQByK ⟨a, ha⟩)⁻¹
  rw [show (⟨b, hb⟩ : ↥hyp.K) = (⟨a, ha⟩ : ↥hyp.K)⁻¹ from Subtype.ext hab, map_inv]

/-- `kActor` turns powers into powers, likewise.  §3 (3) needs it at `n = 2`: the scalar
of `a²` on `Q/Q₀` is the square of that of `a`. -/
theorem kActor_eq_pow {a b : G} (ha : a ∈ hyp.K) (hb : b ∈ hyp.K) (n : ℕ) (hab : b = a ^ n) :
    hyp.kActor hb = (hyp.kActor ha) ^ n := by
  apply Subtype.ext
  change hyp.conjQByK ⟨b, hb⟩ = (hyp.conjQByK ⟨a, ha⟩) ^ n
  rw [show (⟨b, hb⟩ : ↥hyp.K) = (⟨a, ha⟩ : ↥hyp.K) ^ n from Subtype.ext (by simpa using hab),
    map_pow]

/-- Conjugating an element of `Q₀` by `a ∈ K` is `centerKHom` at the corresponding
actor. -/
theorem toCenter_conj {m : ℕ} (s : hyp.LemmaFiveSetup m) {a : G} (ha : a ∈ hyp.K)
    {x : G} (hx : x ∈ hyp.Q0) :
    hyp.toCenter s (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D ha) hx)
      = hyp.centerKHom (hyp.kActor ha) (hyp.toCenter s hx) := by
  apply Subtype.ext
  rw [hyp.centerKHom_apply_val]
  rfl

/-- **The `K`-action in coordinates**: conjugation by `a ∈ K` multiplies the coordinate
by `μ(a)^d`.

This is the book's `c^a = a^{1+θ} c` (p. 119), with `a^{1+θ}` presented as the integer
power `μ(a)^d` that `exists_center_coordinate_equiv` produces. -/
theorem centerCoord_conj {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    {a : G} (ha : a ∈ hyp.K) {x : G} (hx : x ∈ hyp.Q0) :
    hyp.centerCoord s M ι (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D ha) hx)
      = ((M.mu (hyp.kActor ha, 1) ^ d : M.Eˣ) : M.E) * hyp.centerCoord s M ι hx := by
  simp only [centerCoord, hyp.toCenter_conj s ha hx]
  exact hequiv (hyp.kActor ha) (hyp.toCenter s hx)

/-- **Step (10)'s hypothesis, in the coordinates of the standard model**
(Peterfalvi Part II, p. 125).

The group-theoretic hypothesis of `stepTen` — `y · s'^{a⁻¹} = s'^c` — holds exactly when

  `coord y + μ(a)^d · coord s' = μ(c)^d · coord s'`.

Dividing by `coord s' ≠ 0` and writing `α = coord y / coord s'`, this is the book's
`b^{1+θ} = α + a^{-(1+θ)}`: the book normalizes the model so that `s ↦ (0,1)`, i.e.
`coord s' = 1`, but no such normalization is needed — the ratio carries it.

Both conjugations are written in the shape `k · x · k⁻¹`; a caller matching the book's
`s^b = b⁻¹ s b` instantiates `c := b⁻¹`. -/
theorem stepTen_coord {m : ℕ} (s : hyp.LemmaFiveSetup m) (M : hyp.QuotientFieldModel m)
    (ι : Additive ↥(Subgroup.center hyp.Q) ≃+
      ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) (d : ℤ)
    (hequiv : ∀ (k : ↥hyp.actualKActor) (z : ↥(Subgroup.center hyp.Q)),
      ((ι (Additive.ofMul (hyp.centerKHom k z)) :
          ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E)
        = ((M.mu (k, 1) ^ d : M.Eˣ) : M.E) *
          ((ι (Additive.ofMul z) :
            ↥(OddOrder.FiniteField.frobFixedSubfield M.E 2 m)) : M.E))
    {y s' a c : G} (hy : y ∈ hyp.Q0) (hs' : s' ∈ hyp.Q0) (ha : a ∈ hyp.K)
    (hc : c ∈ hyp.K) :
    y * (a * s' * a⁻¹) = c * s' * c⁻¹ ↔
      hyp.centerCoord s M ι hy
          + ((M.mu (hyp.kActor ha, 1) ^ d : M.Eˣ) : M.E) * hyp.centerCoord s M ι hs'
        = ((M.mu (hyp.kActor hc, 1) ^ d : M.Eˣ) : M.E) * hyp.centerCoord s M ι hs' := by
  rw [hyp.eq_iff_centerCoord_eq s M ι
      (hyp.Q0.mul_mem hy (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D ha) hs'))
      (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D hc) hs'),
    hyp.centerCoord_mul s M ι hy (hyp.conj_mem_Q0_of_mem_D (hyp.K_le_D ha) hs'),
    hyp.centerCoord_conj s M ι d hequiv ha hs',
    hyp.centerCoord_conj s M ι d hequiv hc hs']

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
