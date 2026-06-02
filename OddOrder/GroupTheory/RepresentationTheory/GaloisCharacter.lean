import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Complex.Basic
import OddOrder.GroupTheory.RepresentationTheory.ClassFunction
import OddOrder.GroupTheory.RepresentationTheory.IrrIndexing

/-!
# Galois actions on class functions

This file contains coefficientwise automorphism infrastructure for class functions.  The
main operation is `ClassFunction.mapRingEquiv σ φ`, sending `g ↦ σ (φ g)` for a ring
automorphism `σ : ℂ ≃+* ℂ`.

The API is intentionally at the class-function and integral-lattice level.  Proving that a
field automorphism permutes irreducible characters is a deeper representation-theoretic
statement; this file packages the reusable API conditional on that preservation theorem.
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

/-- A coefficientwise automorphism of `ℂ` preserves the irreducible characters of `G`.

This is the explicit representation-theoretic input needed to turn `ClassFunction.mapRingEquiv`
into a permutation of `Irr(G)`.  For Peterfalvi's cyclotomic Galois automorphisms this is the
usual "Galois conjugates of irreducible characters are irreducible" theorem; the present file
keeps that theorem as a named hypothesis and develops the downstream API from it. -/
def PreservesIrreducibleCharacters (G : Type*) [Group G] (σ : ℂ ≃+* ℂ) : Prop :=
  ∀ χ : IrreducibleCharacter G,
    IsIrreducibleCharacter
      (ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ))

theorem preservesIrreducibleCharacters_refl (G : Type*) [Group G] :
    PreservesIrreducibleCharacters G (RingEquiv.refl ℂ) := by
  intro χ
  simp

namespace IrreducibleCharacter

variable {G : Type*} [Group G]

/-- The irreducible character obtained by coefficientwise Galois transport, conditional on
irreducible-character preservation. -/
noncomputable def galoisMap (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ) (χ : IrreducibleCharacter G) :
    IrreducibleCharacter G :=
  ⟨ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ), hσ χ⟩

@[simp] theorem galoisMap_apply_coe (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ) (χ : IrreducibleCharacter G) :
    ((galoisMap σ hσ χ : IrreducibleCharacter G) : ClassFunction G ℂ) =
      ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ) :=
  rfl

@[simp] theorem galoisMap_apply_apply (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ) (χ : IrreducibleCharacter G) (g : G) :
    ((galoisMap σ hσ χ : IrreducibleCharacter G) : ClassFunction G ℂ) g =
      σ ((χ : ClassFunction G ℂ) g) :=
  rfl

@[simp] theorem galoisMap_refl (χ : IrreducibleCharacter G) :
    galoisMap (RingEquiv.refl ℂ) (preservesIrreducibleCharacters_refl G) χ = χ := by
  apply IrreducibleCharacter.ext
  simp [galoisMap]

/-- A coefficientwise automorphism gives a permutation of `Irr(G)` once both it and its inverse
are known to preserve irreducible characters. -/
noncomputable def galoisPerm (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    (hσsymm : PreservesIrreducibleCharacters G σ.symm) :
    Equiv.Perm (IrreducibleCharacter G) where
  toFun := galoisMap σ hσ
  invFun := galoisMap σ.symm hσsymm
  left_inv χ := by
    apply IrreducibleCharacter.ext
    simp [galoisMap]
  right_inv χ := by
    apply IrreducibleCharacter.ext
    simp [galoisMap]

@[simp] theorem galoisPerm_apply_coe (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    (hσsymm : PreservesIrreducibleCharacters G σ.symm)
    (χ : IrreducibleCharacter G) :
    ((galoisPerm σ hσ hσsymm χ : IrreducibleCharacter G) : ClassFunction G ℂ) =
      ClassFunction.mapRingEquiv σ (χ : ClassFunction G ℂ) :=
  rfl

@[simp] theorem galoisPerm_apply_apply (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    (hσsymm : PreservesIrreducibleCharacters G σ.symm)
    (χ : IrreducibleCharacter G) (g : G) :
    ((galoisPerm σ hσ hσsymm χ : IrreducibleCharacter G) : ClassFunction G ℂ) g =
      σ ((χ : ClassFunction G ℂ) g) :=
  rfl

@[simp] theorem galoisPerm_refl :
    galoisPerm (G := G) (RingEquiv.refl ℂ)
      (preservesIrreducibleCharacters_refl G) (preservesIrreducibleCharacters_refl G) =
        Equiv.refl (IrreducibleCharacter G) := by
  ext χ g
  simp [galoisPerm, galoisMap]

theorem galoisPerm_symm (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    (hσsymm : PreservesIrreducibleCharacters G σ.symm) :
    (galoisPerm σ hσ hσsymm).symm = galoisPerm σ.symm hσsymm hσ := by
  ext χ g
  rfl

end IrreducibleCharacter

namespace ClassFunction

variable {G : Type*} [Group G]

/-- A coefficientwise automorphism preserving irreducible characters sends `Irr(G)` into
`Irr(G)`. -/
theorem mapRingEquiv_mem_irreducibleCharacters (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    {φ : ClassFunction G ℂ} (hφ : φ ∈ irreducibleCharacters G) :
    mapRingEquiv σ φ ∈ irreducibleCharacters G :=
  hσ ⟨φ, hφ⟩

/-- A coefficientwise automorphism preserving irreducible characters preserves the virtual
character lattice `ℤ[Irr G]`. -/
theorem mapRingEquiv_mem_ZIrr (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) :
    mapRingEquiv σ φ ∈ ZIrr G := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      exact IsIrreducibleCharacter.mem_ZIrr
        (mapRingEquiv_mem_irreducibleCharacters σ hσ hx)
  | zero =>
      rw [mapRingEquiv_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [mapRingEquiv_add]
      exact Submodule.add_mem _ hx hy
  | smul n x _ hx =>
      rw [mapRingEquiv_zsmul]
      exact Submodule.smul_mem _ n hx

/-- Membership in the virtual-character lattice is invariant under a coefficientwise automorphism
when the automorphism and its inverse preserve irreducible characters. -/
theorem mapRingEquiv_mem_ZIrr_iff (σ : ℂ ≃+* ℂ)
    (hσ : PreservesIrreducibleCharacters G σ)
    (hσsymm : PreservesIrreducibleCharacters G σ.symm)
    {φ : ClassFunction G ℂ} :
    mapRingEquiv σ φ ∈ ZIrr G ↔ φ ∈ ZIrr G := by
  constructor
  · intro hφ
    have hφ' := mapRingEquiv_mem_ZIrr σ.symm hσsymm hφ
    simpa using hφ'
  · exact mapRingEquiv_mem_ZIrr σ hσ

end ClassFunction

end OddOrder.RepresentationTheory
