/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RepresentationTheory.Irreducible

/-!
# Frobenius-conjugate coordinates for finite-field Singer models

For a finite extension `K / 𝔽₂`, scalar extension has the canonical
Frobenius-coordinate isomorphism

`K ⊗[𝔽₂] K ≃ₗ[K] (Fin [K : 𝔽₂] → K)`,

which sends `a ⊗ x` to `(a * x^(2^i))ᵢ`.  Its coordinate basis therefore
gives the exact expansion

`1 ⊗ x = ∑ i, x^(2^i) • b i`.

The final theorem also packages a faithful irreducible abelian
`𝔽₂`-representation as multiplication through an embedding into a Galois
field.  Together these constructions give the normalized coordinates used in
Higman's square-map formula without a primitive-root hypothesis.
-/

set_option autoImplicit false

open scoped TensorProduct BigOperators
open Module

namespace OddOrder.RepresentationTheory

universe uK uV

section FrobeniusCoordinates

variable (K : Type uK) [Field K] [Finite K] [Algebra (ZMod 2) K]

/-- The tuple of the Frobenius conjugates of an element of a finite
`𝔽₂`-extension. -/
noncomputable def frobeniusTupleLinearMap :
    K →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) K) → K) where
  toFun x i := (FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val) x
  map_add' x y := by
    ext i
    exact map_add _ x y
  map_smul' c x := by
    ext i
    exact map_smul (FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val) c x

/-- The scalar extension of `frobeniusTupleLinearMap`. On a pure tensor it is
`a ⊗ x ↦ (a * x^(2^i))ᵢ`. -/
noncomputable def frobeniusTensorCoordinates :
    K ⊗[ZMod 2] K →ₗ[K] (Fin (Module.finrank (ZMod 2) K) → K) :=
  (frobeniusTupleLinearMap K).liftBaseChange K

/-- The family of Frobenius powers, bundled as `𝔽₂`-linear maps. -/
noncomputable def frobeniusLinearFamily :
    Fin (Module.finrank (ZMod 2) K) → (K →ₗ[ZMod 2] K) :=
  fun i => (FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val).toLinearMap

/-- Distinct Frobenius powers are linearly independent over the target
field. -/
theorem linearIndependent_frobeniusLinearFamily :
    LinearIndependent K (frobeniusLinearFamily K) := by
  change LinearIndependent K
    (AlgHom.toLinearMap ∘
      fun i : Fin (Module.finrank (ZMod 2) K) =>
        FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val)
  exact (linearIndependent_algHom_toLinearMap (ZMod 2) K K).comp
    (fun i : Fin (Module.finrank (ZMod 2) K) =>
      FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val)
    (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) K).injective

/-- The Frobenius-conjugate tuples span the full coordinate space. -/
theorem span_range_frobeniusTupleLinearMap :
    Submodule.span K (Set.range (frobeniusTupleLinearMap K)) = ⊤ := by
  change Submodule.span K
    (Set.range fun x => frobeniusTupleLinearMap K x) = ⊤
  have hliFun : LinearIndependent K
      ((LinearMap.ltoFun (ZMod 2) K K K) ∘ frobeniusLinearFamily K) :=
    (linearIndependent_frobeniusLinearFamily K).map'
      (LinearMap.ltoFun (ZMod 2) K K K)
      (LinearMap.ker_eq_bot_of_injective LinearMap.coe_injective)
  have hfun : (fun x => frobeniusTupleLinearMap K x) =
      flip ((LinearMap.ltoFun (ZMod 2) K K K) ∘
        frobeniusLinearFamily K) := by
    funext x i
    rfl
  rw [hfun]
  exact span_flip_eq_top_iff_linearIndependent.mpr hliFun

/-- The Frobenius tensor-coordinate map is surjective. -/
theorem surjective_frobeniusTensorCoordinates :
    Function.Surjective (frobeniusTensorCoordinates K) := by
  rw [← LinearMap.range_eq_top, frobeniusTensorCoordinates,
    LinearMap.range_liftBaseChange]
  exact span_range_frobeniusTupleLinearMap K

omit [Finite K] in
/-- The domain has dimension `[K : 𝔽₂]` over `K`. -/
theorem finrank_frobeniusTensorCoordinates_domain :
    Module.finrank K (K ⊗[ZMod 2] K) =
      Module.finrank (ZMod 2) K :=
  Module.finrank_baseChange

omit [Finite K] in
/-- The Frobenius tuple space has dimension `[K : 𝔽₂]` over `K`. -/
theorem finrank_frobeniusTensorCoordinates_codomain :
    Module.finrank K
      (Fin (Module.finrank (ZMod 2) K) → K) =
        Module.finrank (ZMod 2) K := by
  simp

/-- The Frobenius tensor-coordinate map is bijective. -/
theorem bijective_frobeniusTensorCoordinates :
    Function.Bijective (frobeniusTensorCoordinates K) := by
  have hdim : Module.finrank K (K ⊗[ZMod 2] K) =
      Module.finrank K
        (Fin (Module.finrank (ZMod 2) K) → K) := by
    rw [finrank_frobeniusTensorCoordinates_domain,
      finrank_frobeniusTensorCoordinates_codomain]
  have hsurj := surjective_frobeniusTensorCoordinates K
  exact
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
        hsurj,
      hsurj⟩

/-- The canonical Frobenius-coordinate equivalence for a finite
`𝔽₂`-extension. -/
noncomputable def frobeniusTensorCoordinateEquiv :
    K ⊗[ZMod 2] K ≃ₗ[K]
      (Fin (Module.finrank (ZMod 2) K) → K) :=
  LinearEquiv.ofBijective (frobeniusTensorCoordinates K)
    (bijective_frobeniusTensorCoordinates K)

@[simp]
theorem frobeniusTensorCoordinateEquiv_apply (z : K ⊗[ZMod 2] K) :
    frobeniusTensorCoordinateEquiv K z =
      frobeniusTensorCoordinates K z :=
  rfl

omit [Finite K] in
@[simp]
theorem frobeniusTupleLinearMap_apply (x : K)
    (i : Fin (Module.finrank (ZMod 2) K)) :
    frobeniusTupleLinearMap K x i = x ^ (2 ^ i.val) := by
  simp [frobeniusTupleLinearMap, AlgHom.coe_pow,
    FiniteField.coe_frobeniusAlgHom, pow_iterate]

omit [Finite K] in
@[simp]
theorem frobeniusTensorCoordinates_tmul (a x : K) :
    frobeniusTensorCoordinates K (a ⊗ₜ[ZMod 2] x) =
      fun i : Fin (Module.finrank (ZMod 2) K) =>
        a * x ^ (2 ^ i.val) := by
  ext i
  simp [frobeniusTensorCoordinates]

omit [Finite K] in
@[simp]
theorem frobeniusTensorCoordinates_includeRight (x : K) :
    frobeniusTensorCoordinates K
        (Algebra.TensorProduct.includeRight x) =
      fun i : Fin (Module.finrank (ZMod 2) K) =>
        x ^ (2 ^ i.val) := by
  ext i
  simp [Algebra.TensorProduct.includeRight_apply]

/-- The basis dual to the Frobenius tensor-coordinate equivalence. -/
noncomputable def conjugateTensorBasis :
    Basis (Fin (Module.finrank (ZMod 2) K)) K
      (K ⊗[ZMod 2] K) :=
  Basis.ofEquivFun (frobeniusTensorCoordinateEquiv K)

@[simp]
theorem conjugateTensorBasis_repr_apply (z : K ⊗[ZMod 2] K)
    (i : Fin (Module.finrank (ZMod 2) K)) :
    (conjugateTensorBasis K).repr z i =
      frobeniusTensorCoordinates K z i :=
  rfl

@[simp]
theorem conjugateTensorBasis_repr_includeRight (x : K)
    (i : Fin (Module.finrank (ZMod 2) K)) :
    (conjugateTensorBasis K).repr
        (Algebra.TensorProduct.includeRight x) i =
      x ^ (2 ^ i.val) := by
  simp

/-- The normalized Frobenius-conjugate coordinate expansion. -/
theorem includeRight_eq_sum_conjugateTensorBasis (x : K) :
    Algebra.TensorProduct.includeRight x =
      ∑ i : Fin (Module.finrank (ZMod 2) K),
        x ^ (2 ^ i.val) • conjugateTensorBasis K i := by
  symm
  simpa only [conjugateTensorBasis_repr_includeRight] using
    (conjugateTensorBasis K).sum_repr
      (Algebra.TensorProduct.includeRight x)

omit [Finite K] in
/-- In Frobenius coordinates, scalar extension of multiplication by `u` on
the second tensor factor is diagonal with weights `u^(2^i)`. -/
theorem frobeniusTensorCoordinates_baseChange_lmul_apply
    (u : K) (z : K ⊗[ZMod 2] K)
    (i : Fin (Module.finrank (ZMod 2) K)) :
    frobeniusTensorCoordinates K
        ((Algebra.lmul (ZMod 2) K u).baseChange K z) i =
      u ^ (2 ^ i.val) * frobeniusTensorCoordinates K z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      simp [mul_pow, mul_left_comm]
  | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy, mul_add]

/-- The normalized conjugate basis diagonalizes multiplication by every field
element, with its Frobenius conjugates as eigenvalues. -/
theorem baseChange_lmul_conjugateTensorBasis
    (u : K) (i : Fin (Module.finrank (ZMod 2) K)) :
    (Algebra.lmul (ZMod 2) K u).baseChange K
        (conjugateTensorBasis K i) =
      u ^ (2 ^ i.val) • conjugateTensorBasis K i := by
  apply (frobeniusTensorCoordinateEquiv K).injective
  ext j
  simp only [frobeniusTensorCoordinateEquiv_apply,
    frobeniusTensorCoordinates_baseChange_lmul_apply, map_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [← conjugateTensorBasis_repr_apply,
    Basis.repr_self_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

section TransportedBasis

variable {V : Type uV} [AddCommGroup V] [Module (ZMod 2) V]

/-- Transport the normalized conjugate basis from `K ⊗ K` to the scalar
extension of any `𝔽₂`-space identified linearly with `K`. -/
noncomputable def conjugateTensorBasisOfLinearEquiv
    (e : V ≃ₗ[ZMod 2] K) :
    Basis (Fin (Module.finrank (ZMod 2) K)) K
      (K ⊗[ZMod 2] V) :=
  (conjugateTensorBasis K).map
    (e.baseChange (ZMod 2) K).symm

/-- In the transported basis, every ground vector has the normalized
Frobenius-power coordinate expansion. -/
theorem one_tmul_eq_sum_conjugateTensorBasisOfLinearEquiv
    (e : V ≃ₗ[ZMod 2] K) (v : V) :
    (1 : K) ⊗ₜ[ZMod 2] v =
      ∑ i : Fin (Module.finrank (ZMod 2) K),
        (e v) ^ (2 ^ i.val) •
          conjugateTensorBasisOfLinearEquiv K e i := by
  apply (e.baseChange (ZMod 2) K).injective
  simpa [conjugateTensorBasisOfLinearEquiv,
    Algebra.TensorProduct.includeRight_apply] using
    includeRight_eq_sum_conjugateTensorBasis K (e v)

omit [Finite K] in
/-- A linear equivalence compatible with multiplication intertwines the
corresponding scalar-extended endomorphisms. -/
theorem baseChange_intertwine_of_linearEquiv_mul_compat
    (e : V ≃ₗ[ZMod 2] K) (T : Module.End (ZMod 2) V)
    (u : K) (hcompat : ∀ v, e (T v) = u * e v)
    (z : K ⊗[ZMod 2] V) :
    (e.baseChange (ZMod 2) K V K) (T.baseChange K z) =
      (Algebra.lmul (ZMod 2) K u).baseChange K
        ((e.baseChange (ZMod 2) K V K) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [hcompat]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every compatible multiplication operator is diagonal in the transported
conjugate basis. -/
theorem baseChange_eigen_conjugateTensorBasisOfLinearEquiv
    (e : V ≃ₗ[ZMod 2] K) (T : Module.End (ZMod 2) V)
    (u : K) (hcompat : ∀ v, e (T v) = u * e v)
    (i : Fin (Module.finrank (ZMod 2) K)) :
    T.baseChange K (conjugateTensorBasisOfLinearEquiv K e i) =
      u ^ (2 ^ i.val) •
        conjugateTensorBasisOfLinearEquiv K e i := by
  apply (e.baseChange (ZMod 2) K).injective
  rw [baseChange_intertwine_of_linearEquiv_mul_compat
    K e T u hcompat]
  simpa [conjugateTensorBasisOfLinearEquiv] using
    baseChange_lmul_conjugateTensorBasis K u i

end TransportedBasis

end FrobeniusCoordinates

universe uSinger

/-- A faithful irreducible `𝔽₂`-representation of an abelian group is,
after a linear change of coordinates, multiplication through an embedding into
the units of the Galois field of the same dimension. -/
theorem exists_galoisFieldLinearModel_of_faithful_irreducible
    {C V : Type uSinger} [CommGroup C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (rho : Representation (ZMod 2) C V)
    (n : ℕ) (hn : n ≠ 0)
    (hfin : Module.finrank (ZMod 2) V = n)
    (hirr : Representation.IsIrreducible rho)
    (hfaith : Function.Injective rho) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 n)
      (mu : C →* (GaloisField 2 n)ˣ),
      Function.Injective mu ∧
      ∀ (c : C) (v : V),
        e (rho c v) = (mu c : GaloisField 2 n) * e v := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  letI : Module (MonoidAlgebra (ZMod 2) C) V :=
    Module.compHom V (rho.asAlgebraHom).toRingHom
  have hsmul : ∀ (g : C) (v : V),
      MonoidAlgebra.of (ZMod 2) C g • v = rho g v := by
    intro g v
    change rho.asAlgebraHom
      (MonoidAlgebra.of (ZMod 2) C g) v = rho g v
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod 2) C) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hirr
  have hfaith' : ∀ g : C,
      (∀ v : V,
        MonoidAlgebra.of (ZMod 2) C g • v = v) → g = 1 := by
    intro g hg
    apply hfaith
    rw [map_one]
    ext v
    rw [Module.End.one_apply, ← hsmul g v]
    exact hg v
  have hcardV : Nat.card V = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hfin,
      Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨e0, mu, hmu, hcompat⟩ :=
    exists_galoisField_repr_of_faithful_irreducible
      (p := 2) (C := C) (M := V) hn hcardV hfaith'
  let e : V ≃ₗ[ZMod 2] GaloisField 2 n :=
    { e0 with map_smul' := ZMod.map_smul e0.toAddMonoidHom }
  refine ⟨e, mu, hmu, ?_⟩
  intro c v
  change e0 (rho c v) =
    (mu c : GaloisField 2 n) * e0 v
  rw [← hsmul c v]
  exact hcompat c v

/-- A faithful irreducible abelian representation admits a simultaneous
Frobenius-conjugate eigenbasis over its Singer field model. Every ground
vector has the normalized Frobenius-power coordinates in that same basis. -/
theorem exists_singerConjugateBasis_of_faithful_irreducible
    {C V : Type uSinger} [CommGroup C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (rho : Representation (ZMod 2) C V)
    (m : ℕ) (hm : m ≠ 0)
    (hfin : Module.finrank (ZMod 2) V = m)
    (hirr : Representation.IsIrreducible rho)
    (hfaith : Function.Injective rho) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 m)
      (mu : C →* (GaloisField 2 m)ˣ)
      (b : Basis
        (Fin (Module.finrank (ZMod 2) (GaloisField 2 m)))
        (GaloisField 2 m)
        (GaloisField 2 m ⊗[ZMod 2] V)),
      Function.Injective mu ∧
      b = conjugateTensorBasisOfLinearEquiv (GaloisField 2 m) e ∧
      (∀ (c : C) (v : V),
        e (rho c v) = (mu c : GaloisField 2 m) * e v) ∧
      (∀ v : V,
        (1 : GaloisField 2 m) ⊗ₜ[ZMod 2] v =
          ∑ i : Fin
              (Module.finrank (ZMod 2) (GaloisField 2 m)),
            (e v) ^ (2 ^ i.val) • b i) ∧
      ∀ (c : C)
        (i : Fin
          (Module.finrank (ZMod 2) (GaloisField 2 m))),
        (rho c).baseChange (GaloisField 2 m) (b i) =
          ((mu c : GaloisField 2 m) ^ (2 ^ i.val)) • b i := by
  obtain ⟨e, mu, hmu, hcompat⟩ :=
    exists_galoisFieldLinearModel_of_faithful_irreducible
      rho m hm hfin hirr hfaith
  let b :=
    conjugateTensorBasisOfLinearEquiv (GaloisField 2 m) e
  refine ⟨e, mu, b, hmu, rfl, hcompat, ?_, ?_⟩
  · intro v
    exact one_tmul_eq_sum_conjugateTensorBasisOfLinearEquiv
      (GaloisField 2 m) e v
  · intro c i
    exact baseChange_eigen_conjugateTensorBasisOfLinearEquiv
      (GaloisField 2 m) e (rho c)
      (mu c : GaloisField 2 m) (hcompat c) i

end OddOrder.RepresentationTheory
