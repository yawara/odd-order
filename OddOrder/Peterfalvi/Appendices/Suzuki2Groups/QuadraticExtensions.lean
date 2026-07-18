/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Tactic.Abel

/-!
# Peterfalvi Appendix III: central extensions from quadratic maps

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Lemma 1(b), pp. 139--140.

Given a bilinear map `B : V × V → W`, this file puts the twisted group law

`(v, w) * (v', w') = (v + v', B v v' + w + w')`

on `V × W`.  A quadratic map `q : V → W` over `F₂`, together with an ordered
basis of `V`, supplies such a bilinear lift through `q.toBilin`.  The resulting
short exact sequence has central kernel `W`, quotient `V`, and its squaring map
is exactly `q`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

noncomputable section

open LinearMap (BilinMap)
open Module

universe uR uV uW uI

section BilinearTwistedProduct

variable {R : Type uR} {V : Type uV} {W : Type uW}
  [CommRing R] [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

/-- The twisted product associated with a bilinear map `B : V × V → W`.

The first coordinate is the quotient coordinate and the second coordinate is
the central-kernel coordinate. -/
@[ext]
structure BilinearTwistedProduct (B : BilinMap R V W) where
  quotient : V
  central : W

namespace BilinearTwistedProduct

variable {B : BilinMap R V W}

instance : Mul (BilinearTwistedProduct B) where
  mul x y :=
    ⟨x.quotient + y.quotient,
      B x.quotient y.quotient + x.central + y.central⟩

instance : One (BilinearTwistedProduct B) where
  one := ⟨0, 0⟩

instance : Inv (BilinearTwistedProduct B) where
  inv x := ⟨-x.quotient, B x.quotient x.quotient - x.central⟩

/-- Multiplication in twisted-product coordinates. -/
theorem mul_def (x y : BilinearTwistedProduct B) :
    x * y =
      ⟨x.quotient + y.quotient,
        B x.quotient y.quotient + x.central + y.central⟩ :=
  rfl

/-- The identity in twisted-product coordinates. -/
theorem one_def : (1 : BilinearTwistedProduct B) = ⟨0, 0⟩ :=
  rfl

/-- Inversion in twisted-product coordinates. -/
theorem inv_def (x : BilinearTwistedProduct B) :
    x⁻¹ = ⟨-x.quotient, B x.quotient x.quotient - x.central⟩ :=
  rfl

@[simp]
theorem quotient_mul (x y : BilinearTwistedProduct B) :
    (x * y).quotient = x.quotient + y.quotient :=
  rfl

@[simp]
theorem central_mul (x y : BilinearTwistedProduct B) :
    (x * y).central = B x.quotient y.quotient + x.central + y.central :=
  rfl

@[simp]
theorem quotient_one : (1 : BilinearTwistedProduct B).quotient = 0 :=
  rfl

@[simp]
theorem central_one : (1 : BilinearTwistedProduct B).central = 0 :=
  rfl

@[simp]
theorem quotient_inv (x : BilinearTwistedProduct B) :
    x⁻¹.quotient = -x.quotient :=
  rfl

@[simp]
theorem central_inv (x : BilinearTwistedProduct B) :
    x⁻¹.central = B x.quotient x.quotient - x.central :=
  rfl

/-- Bilinearity is precisely the cocycle identity needed for associativity. -/
instance : Group (BilinearTwistedProduct B) where
  mul_assoc x y z := by
    ext
    · exact add_assoc _ _ _
    · simp only [central_mul, quotient_mul, map_add, LinearMap.add_apply]
      abel
  one_mul x := by
    ext <;> simp
  mul_one x := by
    ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp
    · simp only [central_mul, central_inv, quotient_inv, map_neg,
        LinearMap.neg_apply, central_one]
      abel

/-- The central-coordinate inclusion. -/
def centralEmbedding (B : BilinMap R V W) :
    Multiplicative W →* BilinearTwistedProduct B where
  toFun w := ⟨0, w.toAdd⟩
  map_one' := by ext <;> rfl
  map_mul' x y := by ext <;> simp

@[simp]
theorem centralEmbedding_quotient (w : Multiplicative W) :
    (centralEmbedding B w).quotient = 0 :=
  rfl

@[simp]
theorem centralEmbedding_central (w : Multiplicative W) :
    (centralEmbedding B w).central = w.toAdd :=
  rfl

/-- The central-coordinate inclusion is injective. -/
theorem centralEmbedding_injective :
    Function.Injective (centralEmbedding B) := by
  intro x y h
  exact Multiplicative.toAdd.injective
    (congrArg BilinearTwistedProduct.central h)

/-- The image of the kernel coordinate is central. -/
theorem centralEmbedding_range_le_center :
    (centralEmbedding B).range ≤ Subgroup.center (BilinearTwistedProduct B) := by
  rintro x ⟨w, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  ext
  · simp
  · simp [mul_def, add_comm]

/-- Projection to the quotient coordinate. -/
def projection (B : BilinMap R V W) :
    BilinearTwistedProduct B →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.quotient
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem projection_apply (x : BilinearTwistedProduct B) :
    (projection B x).toAdd = x.quotient :=
  rfl

/-- Projection onto the quotient coordinate is surjective. -/
theorem projection_surjective : Function.Surjective (projection B) := by
  intro v
  exact ⟨⟨v.toAdd, 0⟩, rfl⟩

/-- The central coordinate is exactly the kernel of the quotient projection. -/
theorem range_centralEmbedding_eq_ker_projection :
    (centralEmbedding B).range = (projection B).ker := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hx
    have hx0 : x.quotient = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa using h
    refine ⟨Multiplicative.ofAdd x.central, ?_⟩
    ext
    · exact hx0.symm
    · rfl

/-- The twisted product is a short exact sequence
`1 → W → V ×_B W → V → 1`. -/
def groupExtension (B : BilinMap R V W) :
    GroupExtension (Multiplicative W) (BilinearTwistedProduct B)
      (Multiplicative V) where
  inl := centralEmbedding B
  rightHom := projection B
  inl_injective := centralEmbedding_injective
  range_inl_eq_ker_rightHom := range_centralEmbedding_eq_ker_projection
  rightHom_surjective := projection_surjective

end BilinearTwistedProduct

end BilinearTwistedProduct

section QuadraticExtension

variable {V : Type uV} {W : Type uW} {ι : Type uI}
  [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
  [LinearOrder ι]

/-- Peterfalvi's central extension attached to `q`, using the upper-triangular
bilinear lift selected by the ordered basis `basis`. -/
abbrev QuadraticExtension (q : QuadraticMap (ZMod 2) V W)
    (basis : Basis ι (ZMod 2) V) :=
  BilinearTwistedProduct (q.toBilin basis)

namespace QuadraticExtension

variable (q : QuadraticMap (ZMod 2) V W)
  (basis : Basis ι (ZMod 2) V)

/-- The chosen bilinear lift has diagonal equal to the original quadratic map. -/
theorem toBilin_self (v : V) : q.toBilin basis v v = q v := by
  have h := QuadraticMap.congr_fun
    (QuadraticMap.toQuadraticMap_toBilin q basis) v
  simpa only [LinearMap.BilinMap.toQuadraticMap_apply] using h

/-- Addition is self-cancelling in a module over `F₂`. -/
private theorem add_self_eq_zero (w : W) : w + w = 0 := by
  calc
    w + w = 2 • w := (two_nsmul w).symm
    _ = (2 : ZMod 2) • w :=
      (Nat.cast_smul_eq_nsmul (ZMod 2) 2 w).symm
    _ = 0 := by
      rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_smul]

/-- **Peterfalvi Appendix III, Lemma 1(b).**  The explicit twisted product is
a central extension of the additive groups of `W` and `V`. -/
def extension :
    GroupExtension (Multiplicative W) (QuadraticExtension q basis)
      (Multiplicative V) :=
  BilinearTwistedProduct.groupExtension (q.toBilin basis)

/-- The kernel in the quadratic extension is central. -/
theorem range_inl_le_center :
    (extension q basis).inl.range ≤ Subgroup.center (QuadraticExtension q basis) :=
  BilinearTwistedProduct.centralEmbedding_range_le_center

/-- **Peterfalvi Appendix III, Lemma 1(b).**  Squaring in the constructed
central extension recovers `q` under the kernel embedding. -/
theorem sq_eq_inl_q (x : QuadraticExtension q basis) :
    x ^ 2 = (extension q basis).inl (Multiplicative.ofAdd (q x.quotient)) := by
  rw [pow_two]
  ext
  · change x.quotient + x.quotient = 0
    exact add_self_eq_zero x.quotient
  · change q.toBilin basis x.quotient x.quotient + x.central + x.central =
      q x.quotient
    rw [toBilin_self q basis, add_assoc, add_self_eq_zero, add_zero]

end QuadraticExtension

end QuadraticExtension

end


end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
