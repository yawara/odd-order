import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction

/-!
# Galois actions on class functions

This file contains coefficientwise automorphism infrastructure for class functions.  The
main operation is `ClassFunction.mapRingEquiv σ φ`, sending `g ↦ σ (φ g)` for a ring
automorphism `σ : ℂ ≃+* ℂ`.

The API is intentionally at the class-function and integral-lattice level.  Proving that a
field automorphism permutes irreducible characters is a deeper representation-theoretic
statement; downstream code can combine these transport lemmas with such a permutation theorem
when it is available.
-/

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {G : Type*} [Group G]

/-- Apply a ring automorphism of `ℂ` coefficientwise to a class function. -/
def mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) : ClassFunction G ℂ :=
  ⟨fun g => σ (φ g), by
    intro g h
    exact congrArg σ (φ.conj_eq g h)
  ⟩

@[simp] theorem mapRingEquiv_apply (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) (g : G) :
    mapRingEquiv σ φ g = σ (φ g) :=
  rfl

@[simp] theorem mapRingEquiv_zero (σ : ℂ ≃+* ℂ) :
    mapRingEquiv (G := G) σ 0 = 0 := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_add (σ : ℂ ≃+* ℂ) (φ ψ : ClassFunction G ℂ) :
    mapRingEquiv σ (φ + ψ) = mapRingEquiv σ φ + mapRingEquiv σ ψ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_neg (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ (-φ) = -mapRingEquiv σ φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_sub (σ : ℂ ≃+* ℂ) (φ ψ : ClassFunction G ℂ) :
    mapRingEquiv σ (φ - ψ) = mapRingEquiv σ φ - mapRingEquiv σ ψ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem zsmul_apply (n : ℤ) (φ : ClassFunction G ℂ) (g : G) :
    (n • φ) g = n • φ g := rfl

@[simp] theorem mapRingEquiv_zsmul (σ : ℂ ≃+* ℂ) (n : ℤ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ (n • φ) = n • mapRingEquiv σ φ := by
  ext g
  simp [mapRingEquiv]

/-- Coefficientwise automorphism as a `ℤ`-linear map of class functions. -/
def mapRingEquivLinear (σ : ℂ ≃+* ℂ) : (ClassFunction G ℂ →ₗ[ℤ] ClassFunction G ℂ) :=
  { toFun := mapRingEquiv σ
    map_add' := fun φ ψ => mapRingEquiv_add σ φ ψ
    map_smul' := fun n φ => mapRingEquiv_zsmul σ n φ }

@[simp] theorem mapRingEquivLinear_apply (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquivLinear (G := G) σ φ = mapRingEquiv σ φ :=
  rfl

@[simp] theorem mapRingEquiv_refl (φ : ClassFunction G ℂ) :
    mapRingEquiv (RingEquiv.refl ℂ) φ = φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_symm_mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ.symm (mapRingEquiv σ φ) = φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_mapRingEquiv_symm (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ (mapRingEquiv σ.symm φ) = φ := by
  ext g
  simp [mapRingEquiv]

@[simp] theorem mapRingEquiv_eq_zero_iff (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    simpa using congrArg (mapRingEquiv σ.symm) h
  · intro h
    simp [h]

@[simp] theorem mapRingEquiv_ne_zero_iff (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    mapRingEquiv σ φ ≠ 0 ↔ φ ≠ 0 :=
  not_congr (mapRingEquiv_eq_zero_iff σ φ)

@[simp] theorem mem_support_mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) (g : G) :
    g ∈ (mapRingEquiv σ φ).support ↔ g ∈ φ.support := by
  simp [support, mapRingEquiv]

@[simp] theorem support_mapRingEquiv (σ : ℂ ≃+* ℂ) (φ : ClassFunction G ℂ) :
    (mapRingEquiv σ φ).support = φ.support := by
  ext g
  simp

theorem mapRingEquiv_mem_supportedSubmodule_iff (σ : ℂ ≃+* ℂ)
    {A : Set G} {φ : ClassFunction G ℂ} :
    mapRingEquiv σ φ ∈ supportedSubmodule (G := G) (k := ℂ) A ↔
      φ ∈ supportedSubmodule (G := G) (k := ℂ) A := by
  simp [mem_supportedSubmodule, support_mapRingEquiv]

theorem mapRingEquiv_mem_supportedSubmodule (σ : ℂ ≃+* ℂ)
    {A : Set G} {φ : ClassFunction G ℂ}
    (hφ : φ ∈ supportedSubmodule (G := G) (k := ℂ) A) :
    mapRingEquiv σ φ ∈ supportedSubmodule (G := G) (k := ℂ) A :=
  (mapRingEquiv_mem_supportedSubmodule_iff σ).mpr hφ

theorem mapRingEquiv_innerSum (σ : ℂ ≃+* ℂ)
    (hσ : ∀ z : ℂ, σ (star z) = star (σ z))
    [Fintype G] (φ ψ : ClassFunction G ℂ) :
    innerSum (mapRingEquiv σ φ) (mapRingEquiv σ ψ) = σ (innerSum φ ψ) := by
  rw [innerSum, innerSum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mapRingEquiv_apply, mapRingEquiv_apply, ← hσ (ψ g), map_mul]

/-- Inner products are transported by coefficientwise automorphisms that commute with `star`.

For cyclotomic Galois automorphisms this star-commutation is the usual compatibility with complex
conjugation.  The conclusion is deliberately `σ (inner φ ψ)`, not equality with `inner φ ψ`; the
latter follows in applications when the source inner product lies in the fixed field, e.g. for
integer-valued inner products on an orthonormal integral span. -/
theorem mapRingEquiv_inner (σ : ℂ ≃+* ℂ)
    (hσ : ∀ z : ℂ, σ (star z) = star (σ z))
    [Fintype G] [Invertible (Nat.card G : ℂ)] (φ ψ : ClassFunction G ℂ) :
    inner (mapRingEquiv σ φ) (mapRingEquiv σ ψ) = σ (inner φ ψ) := by
  rw [inner_eq_inv_card_mul_innerSum, inner_eq_inv_card_mul_innerSum, map_mul,
    mapRingEquiv_innerSum σ hσ φ ψ]
  simp

end ClassFunction

end OddOrder.RepresentationTheory
