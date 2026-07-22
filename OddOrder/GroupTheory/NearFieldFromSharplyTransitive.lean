/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.TypeTags.Basic
import OddOrder.Peterfalvi.Appendices.NearFieldClass

/-!
# Near-field from a sharply transitive additive action

Peterfalvi, *Character Theory for the Odd Order Theorem*, Appendix C, p. 137 (the "transport"
recorded in the proof of Proposition 1): if a group `M` acts on an additive abelian group `A` by
*additive* automorphisms, **regularly on the nonzero elements** `A ∖ {0}` (sharply transitive),
then `A` carries a near-field structure whose multiplicative group `A∖{0}` is isomorphic to `M`.

Concretely, fix an element `e ≠ 0` (the multiplicative identity — in the group case, the `D`-fixed
point of `F#`).  For `y ≠ 0` let `m_y ∈ M` be the *unique* element with `m_y • e = y`; define

`x * y := m_y • x`   (and `x * 0 := 0`).

Then `(A, +, *)` is a near-field (`NearField`):

* associativity `(x*y)*z = x*(y*z)` follows from `m_{m_z • y} = m_z * m_y` (uniqueness of `m`);
* `e` is a two-sided identity (`m_e = 1`);
* every `y ≠ 0` is invertible (`y⁻¹ := m_y⁻¹ • e`);
* the **right** distributive law `(x + y)*z = x*z + y*z` is exactly additivity of `z ↦ m_z • ·`.

The construction is packaged through `SharplyTransitiveData`.  This is the elementary core of the
affine near-field model (`AffineNearFieldModel`) of Appendix C, Proposition 1.
-/

open OddOrder.Peterfalvi.Appendices.NearFields (NearField)

namespace OddOrder.GroupTheory

/-- A `MulDistribMulAction M α` on a commutative group `α` (a monoid `M` acting by group
automorphisms) transports to a `DistribMulAction` of `M` on the additive type tag `Additive α`:
the action fixes `0 = Additive.ofMul 1` and is additive because it is multiplicative on `α`.

This is the bridge that turns a conjugation action of a group `Q` on a normal *abelian* subgroup
`F` into the `[DistribMulAction Q (Additive F)]` that `SharplyTransitiveData` consumes. -/
@[reducible] def MulDistribMulAction.toDistribMulActionAdditive {M α : Type*} [Monoid M]
    [CommGroup α] [MulDistribMulAction M α] : DistribMulAction M (Additive α) where
  smul m a := Additive.ofMul (m • a.toMul)
  one_smul a := by
    change Additive.ofMul ((1 : M) • a.toMul) = a
    rw [one_smul]; rfl
  mul_smul m n a := by
    change Additive.ofMul ((m * n) • a.toMul)
      = Additive.ofMul (m • (Additive.ofMul (n • a.toMul)).toMul)
    rw [mul_smul]; rfl
  smul_zero m := by
    change Additive.ofMul (m • (1 : α)) = (0 : Additive α)
    rw [smul_one]; rfl
  smul_add m a b := by
    change Additive.ofMul (m • (a.toMul * b.toMul))
      = Additive.ofMul (m • a.toMul) + Additive.ofMul (m • b.toMul)
    rw [smul_mul']; rfl

variable {M A : Type*} [Group M] [AddCommGroup A] [DistribMulAction M A]

/-- **Data for the near-field transport** (Peterfalvi App. C, p. 137): a group `M` acting on the
additive abelian group `A` by additive automorphisms (`DistribMulAction`), *regularly on the
nonzero elements* — for every `y ≠ 0` there is a unique `m ∈ M` sending the chosen identity `e` to
`y`. -/
structure SharplyTransitiveData (M A : Type*) [Group M] [AddCommGroup A] [DistribMulAction M A]
    where
  /-- The multiplicative identity of the near-field (the `D`-fixed point of `F#`). -/
  e : A
  /-- `e ≠ 0`, so the near-field is nontrivial. -/
  e_ne_zero : e ≠ 0
  /-- `M` acts sharply transitively on `A ∖ {0}`: each nonzero `y` is `m • e` for a unique `m`. -/
  reg : ∀ y : A, y ≠ 0 → ∃! m : M, m • e = y

namespace SharplyTransitiveData

variable (d : SharplyTransitiveData M A)

/-- The unique `m ∈ M` with `m • e = y`, for `y ≠ 0` (and `1` for `y = 0`, an unused convention). -/
noncomputable def coord (y : A) : M := by
  classical exact if hy : y = 0 then 1 else (d.reg y hy).choose

theorem coord_smul_e {y : A} (hy : y ≠ 0) : d.coord y • d.e = y := by
  rw [coord, dif_neg hy]; exact (d.reg y hy).choose_spec.1

/-- Uniqueness: any `m` with `m • e = y` equals `coord y` (for `y ≠ 0`). -/
theorem coord_unique {y : A} (hy : y ≠ 0) {m : M} (hm : m • d.e = y) : m = d.coord y := by
  rw [coord, dif_neg hy]; exact (d.reg y hy).choose_spec.2 m hm

/-- `m • e ≠ 0` for any `m` (as `e ≠ 0` and `m` is invertible). -/
theorem smul_e_ne_zero (m : M) : m • d.e ≠ 0 := by
  intro h
  exact d.e_ne_zero (by rw [← smul_zero m⁻¹, ← h, inv_smul_smul])

/-- The near-field multiplication `x * y = (coord y) • x` (and `x * 0 = 0`). -/
noncomputable def mul (x y : A) : A := by
  classical exact if _hy : y = 0 then 0 else d.coord y • x

theorem mul_def {x y : A} (hy : y ≠ 0) : d.mul x y = d.coord y • x := dif_neg hy

@[simp] theorem mul_zero (x : A) : d.mul x 0 = 0 := dif_pos rfl

@[simp] theorem zero_mul (x : A) : d.mul 0 x = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [d.mul_def hx, smul_zero]

theorem coord_e : d.coord d.e = 1 := (d.coord_unique d.e_ne_zero (one_smul M d.e)).symm

@[simp] theorem mul_e (x : A) : d.mul x d.e = x := by rw [d.mul_def d.e_ne_zero, coord_e, one_smul]

@[simp] theorem e_mul (x : A) (hx : x ≠ 0) : d.mul d.e x = x := by
  rw [d.mul_def hx, coord_smul_e d hx]

/-- `x * y = 0 ↔ x = 0 ∨ y = 0` (no zero divisors): `(coord y) • x = 0` forces `x = 0`. -/
theorem mul_eq_zero_iff {x y : A} : d.mul x y = 0 ↔ x = 0 ∨ y = 0 := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [d.mul_def hy]
    constructor
    · intro h
      refine Or.inl ?_
      rw [← inv_smul_smul (d.coord y) x, h, smul_zero]
    · rintro (hx | hx)
      · rw [hx, smul_zero]
      · exact absurd hx hy

theorem mul_ne_zero {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) : d.mul x y ≠ 0 := by
  rw [Ne, mul_eq_zero_iff]; exact fun h => h.elim hx hy

/-- The key group-theoretic identity: `coord (z • y) = coord z * coord y` for `y ≠ 0`
(so `coord` is an anti-homomorphism; this drives associativity of `mul`). -/
theorem coord_smul {y : A} (hy : y ≠ 0) (m : M) :
    d.coord (m • y) = m * d.coord y := by
  refine (d.coord_unique (by
    intro h; exact hy (by rw [← inv_smul_smul m y, h, smul_zero])) ?_).symm
  rw [mul_smul, coord_smul_e d hy]

/-- **Associativity** `(x * y) * z = x * (y * z)`. -/
theorem mul_assoc' (x y z : A) : d.mul (d.mul x y) z = d.mul x (d.mul y z) := by
  by_cases hz : z = 0
  · simp [hz]
  by_cases hy : y = 0
  · simp [hy]
  · rw [d.mul_def hz, d.mul_def hy, d.mul_def (d.mul_ne_zero hy hz), d.mul_def hz,
      d.coord_smul hy, mul_smul]

/-- `e` is a left identity: `e * x = x`. -/
@[simp] theorem one_mul' (x : A) : d.mul d.e x = x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact d.e_mul x hx

/-- **Right multiplication is the action**: `x * (m • e) = m • x`.  This is the bridge between the
near-field multiplication and the group action — the identity that turns the conjugation action of
the acting group into right multiplication by `F^*` (Peterfalvi's `𝓛(F) = F ⋊ F^*`). -/
theorem mul_smul_e (m : M) (x : A) : d.mul x (m • d.e) = m • x := by
  rw [d.mul_def (d.smul_e_ne_zero m), ← d.coord_unique (d.smul_e_ne_zero m) rfl]

/-- **Right distributivity** `(a + b) * c = a * c + b * c` — exactly additivity of `· • x`. -/
theorem right_distrib' (a b c : A) : d.mul (a + b) c = d.mul a c + d.mul b c := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [d.mul_def hc, d.mul_def hc, d.mul_def hc, smul_add]

/-- The multiplicative inverse `y⁻¹ := (coord y)⁻¹ • e` (and `0⁻¹ = 0`). -/
noncomputable def inv (y : A) : A := by
  classical exact if _hy : y = 0 then 0 else (d.coord y)⁻¹ • d.e

theorem inv_def {y : A} (hy : y ≠ 0) : d.inv y = (d.coord y)⁻¹ • d.e := dif_neg hy

@[simp] theorem inv_zero' : d.inv 0 = 0 := dif_pos rfl

theorem inv_ne_zero {y : A} (hy : y ≠ 0) : d.inv y ≠ 0 := by
  rw [d.inv_def hy]; exact d.smul_e_ne_zero _

theorem coord_inv {y : A} (hy : y ≠ 0) : d.coord (d.inv y) = (d.coord y)⁻¹ := by
  rw [d.inv_def hy, d.coord_smul d.e_ne_zero, coord_e, mul_one]

/-- Every nonzero element is invertible: `y * y⁻¹ = e`. -/
theorem mul_inv_cancel' {y : A} (hy : y ≠ 0) : d.mul y (d.inv y) = d.e := by
  rw [d.mul_def (d.inv_ne_zero hy), d.coord_inv hy, inv_smul_eq_iff]
  exact (d.coord_smul_e hy).symm

/-- **The near-field structure transported from the sharply transitive action** (Peterfalvi
App. C, p. 137).  The additive group is `A`; multiplication is `x * y = (coord y) • x`; the
multiplicative identity is `e`. -/
@[reducible] noncomputable def nearField : NearField A where
  __ := (inferInstance : AddCommGroup A)
  mul := d.mul
  one := d.e
  inv := d.inv
  mul_assoc := d.mul_assoc'
  one_mul := d.one_mul'
  mul_one := d.mul_e
  zero_mul := d.zero_mul
  mul_zero := d.mul_zero
  inv_zero := d.inv_zero'
  mul_inv_cancel := fun _ ha => d.mul_inv_cancel' ha
  exists_pair_ne := ⟨0, d.e, fun h => d.e_ne_zero h.symm⟩
  right_distrib := d.right_distrib'

/-- **The multiplicative group of the near-field is the acting group** `M`: the map
`m ↦ m⁻¹ • e` is a group isomorphism `M ≃* Aˣ` (onto the units `A ∖ {0}` of the near-field).

The inverse `m ↦ m⁻¹` (rather than `m ↦ m • e`) is what makes this a *homomorphism*: right
multiplication is `x * y = (coord y) • x`, so `(m₁⁻¹ • e) * (m₂⁻¹ • e) = (m₁ m₂)⁻¹ • e` — i.e.
`m ↦ m • e` is an *anti*-homomorphism, and pre-composing with inversion fixes the direction.  This
realizes the identification `Q ≃* F^*` of Peterfalvi Appendix C, Proposition 1. -/
noncomputable def mulEquivUnits :
    letI := d.nearField
    M ≃* Aˣ :=
  letI := d.nearField
  { toFun := fun m => Units.mk0 (m⁻¹ • d.e) (d.smul_e_ne_zero _)
    invFun := fun u => (d.coord (u : A))⁻¹
    left_inv := fun m => by
      simp only [Units.val_mk0]
      rw [← d.coord_unique (d.smul_e_ne_zero m⁻¹) rfl, inv_inv]
    right_inv := fun u => by
      have hu : (u : A) ≠ 0 := u.ne_zero
      apply Units.ext
      simp only [Units.val_mk0, inv_inv]
      exact d.coord_smul_e hu
    map_mul' := fun m₁ m₂ => by
      apply Units.ext
      simp only [Units.val_mk0, Units.val_mul]
      change (m₁ * m₂)⁻¹ • d.e = d.mul (m₁⁻¹ • d.e) (m₂⁻¹ • d.e)
      rw [d.mul_smul_e, smul_smul, mul_inv_rev] }

end SharplyTransitiveData

end OddOrder.GroupTheory
