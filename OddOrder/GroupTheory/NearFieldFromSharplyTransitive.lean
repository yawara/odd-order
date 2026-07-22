/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.NearFields

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
  rw [Ne, mul_eq_zero_iff]; tauto

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

end SharplyTransitiveData

end OddOrder.GroupTheory
