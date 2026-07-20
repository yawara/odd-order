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
import Mathlib.NumberTheory.Multiplicity
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

The final section combines this Singer model with a faithful action that is
transitive on the nonzero vectors of a second module.  The two modules must
then have the same dimension over `𝔽₂`; this is the dimension step in Higman's
Lemma 6.
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

/-! ## Faithful transitive Singer actions -/

universe uHelperF uHelperC uHelperV uHelperW uGenerator

/-- In a faithful irreducible representation of a commutative group, every
nontrivial actor has no nonzero fixed vector. -/
theorem representation_fixedVector_eq_zero_of_faithful_irreducible
    {F : Type uHelperF} {C : Type uHelperC} {V : Type uHelperV}
    [Field F] [CommGroup C] [AddCommGroup V] [Module F V]
    (rho : Representation F C V)
    (hirr : Representation.IsIrreducible rho)
    (hfaith : Function.Injective rho)
    (a : C) (ha : a ≠ 1) :
    ∀ v : V, rho a v = v → v = 0 := by
  let d : Module.End F V := rho a - 1
  let W : Subrepresentation rho :=
    { toSubmodule := LinearMap.ker d
      apply_mem_toSubmodule := by
        intro c v hv
        rw [LinearMap.mem_ker] at hv ⊢
        change rho a (rho c v) - rho c v = 0
        change rho a v - v = 0 at hv
        calc
          rho a (rho c v) - rho c v =
              rho c (rho a v) - rho c v := by
                rw [← Module.End.mul_apply, ← Module.End.mul_apply,
                  ← map_mul, ← map_mul, mul_comm]
          _ = 0 := by rw [← map_sub, hv, map_zero] }
  letI : Representation.IsIrreducible rho := hirr
  intro v hv
  have hvW : v ∈ W := by
    change v ∈ LinearMap.ker d
    rw [LinearMap.mem_ker]
    change rho a v - v = 0
    rw [hv, sub_self]
  rcases eq_bot_or_eq_top W with hW | hW
  · rw [hW] at hvW
    change v ∈ (⊥ : Submodule F V) at hvW
    exact (Submodule.mem_bot F).mp hvW
  · have hker : LinearMap.ker d = ⊤ := by
      change W.toSubmodule = ⊤
      rw [hW]
      rfl
    have hd : d = 0 := LinearMap.ker_eq_top.mp hker
    have haRho : rho a = 1 := by
      change rho a = LinearMap.id
      change rho a - 1 = 0 at hd
      exact sub_eq_zero.mp hd
    exact (ha (hfaith (by simpa only [map_one] using haRho))).elim

/-- A faithful action of a commutative group which is transitive on nonzero
vectors has no nonzero fixed vector for a nontrivial actor. -/
theorem representation_fixedVector_eq_zero_of_faithful_transitive_nonzero
    {F : Type uHelperF} {C : Type uHelperC} {V : Type uHelperV}
    [Field F] [CommGroup C] [AddCommGroup V] [Module F V]
    (rho : Representation F C V)
    (hfaith : Function.Injective rho)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      ∃ c : C, rho c v = w)
    (a : C) (ha : a ≠ 1) :
    ∀ v : V, rho a v = v → v = 0 := by
  intro v hv
  by_contra hv0
  have haRho : rho a = 1 := by
    ext w
    by_cases hw : w = 0
    · subst w
      simp
    · obtain ⟨c, hc⟩ := htrans v w hv0 hw
      calc
        rho a w = rho a (rho c v) := by rw [hc]
        _ = rho c (rho a v) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply,
            ← map_mul, ← map_mul, mul_comm]
        _ = rho c v := by rw [hv]
        _ = w := hc
  exact ha (hfaith (by simpa only [map_one] using haRho))

/-- A faithful action of an abelian group which is transitive on the nonzero
vectors is regular there, so the actor has one fewer element than the space. -/
theorem natCard_actor_eq_natCard_sub_one_of_faithful_transitive_nonzero
    {F : Type uHelperF} {C : Type uHelperC} {V : Type uHelperV}
    [Field F] [CommGroup C] [Finite C]
    [AddCommGroup V] [Module F V] [Finite V] [Nontrivial V]
    (rho : Representation F C V)
    (hfaith : Function.Injective rho)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w) :
    Nat.card C = Nat.card V - 1 := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  let orbit : C → {w : V // w ≠ 0} := fun c ↦
    ⟨rho c v, fun hzero ↦ hv (by
      have h := congrArg (rho c⁻¹) hzero
      simpa [← map_mul] using h)⟩
  have horbit_injective : Function.Injective orbit := by
    intro c d hcd
    apply hfaith
    ext w
    by_cases hw : w = 0
    · subst w
      simp
    · obtain ⟨g, hg⟩ := htrans v w hv hw
      have hcv : rho c v = rho d v := Subtype.ext_iff.mp hcd
      calc
        rho c w = rho c (rho g v) := by rw [hg]
        _ = rho (c * g) v := by rw [map_mul]; rfl
        _ = rho (g * c) v := by rw [mul_comm]
        _ = rho g (rho c v) := by rw [map_mul]; rfl
        _ = rho g (rho d v) := by rw [hcv]
        _ = rho (g * d) v := by rw [map_mul]; rfl
        _ = rho (d * g) v := by rw [mul_comm]
        _ = rho d (rho g v) := by rw [map_mul]; rfl
        _ = rho d w := by rw [hg]
  have horbit_surjective : Function.Surjective orbit := by
    intro w
    obtain ⟨c, hc⟩ := htrans v w.1 hv w.2
    exact ⟨c, Subtype.ext hc⟩
  have hcard : Fintype.card C = Fintype.card {w : V // w ≠ 0} :=
    Fintype.card_congr (Equiv.ofBijective orbit ⟨horbit_injective, horbit_surjective⟩)
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard

private theorem three_dvd_two_pow_sub_one_of_even
    {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have h := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hn.two_dvd
  norm_num at h ⊢
  exact h

/-- If a finite commutative group acts faithfully and transitively on the
nonzero vectors of an even-dimensional `𝔽₂`-space, it contains a nonidentity
actor of order three. -/
theorem exists_ne_one_orderOf_eq_three_of_even_faithful_transitive_nonzero
    {C : Type uHelperC} {V : Type uHelperV}
    [CommGroup C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (rho : Representation (ZMod 2) C V)
    (hfaith : Function.Injective rho)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w)
    (hn : Even (Module.finrank (ZMod 2) V)) :
    ∃ a : C, a ≠ 1 ∧ orderOf a = 3 := by
  have hcardV : Nat.card V =
      2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [Nat.card_eq_fintype_card]
  have hcardC : Nat.card C =
      2 ^ Module.finrank (ZMod 2) V - 1 := by
    rw [natCard_actor_eq_natCard_sub_one_of_faithful_transitive_nonzero
      (F := ZMod 2) (C := C) (V := V) rho hfaith htrans,
      hcardV]
  have hdvd : 3 ∣ Nat.card C := by
    rw [hcardC]
    exact three_dvd_two_pow_sub_one_of_even hn
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨a, ?_, ha⟩
  intro haOne
  rw [haOne, orderOf_one] at ha
  omega

/-- Cyclic specialization: a generator of the faithful transitive actor has
full Singer order. -/
theorem exists_generator_orderOf_eq_pow_sub_one_of_faithful_transitive_nonzero
    {C V : Type uGenerator} [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] [Nontrivial V]
    (rho : Representation (ZMod 2) C V)
    (n : ℕ) (hfin : Module.finrank (ZMod 2) V = n)
    (hfaith : Function.Injective rho)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w) :
    ∃ c : C, orderOf c = 2 ^ n - 1 := by
  have hcardV : Nat.card V = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hfin]
    norm_num [Nat.card_eq_fintype_card]
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := C)
  refine ⟨c, (orderOf_eq_card_of_forall_mem_zpowers hc).trans ?_⟩
  rw [natCard_actor_eq_natCard_sub_one_of_faithful_transitive_nonzero
      (F := ZMod 2) (C := C) (V := V) rho hfaith htrans,
    hcardV]

/-- Faithfulness transfers across an equivariant linear equivalence. -/
theorem representation_faithful_of_equivariant_linearEquiv
    {F : Type uHelperF} {C : Type uHelperC}
    {V : Type uHelperV} {W : Type uHelperW}
    [Field F] [Group C]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (rhoV : Representation F C V) (rhoW : Representation F C W)
    (e : V ≃ₗ[F] W)
    (he : ∀ c v, e (rhoV c v) = rhoW c (e v))
    (hfaithV : Function.Injective rhoV) : Function.Injective rhoW := by
  intro c d hcd
  apply hfaithV
  ext v
  apply e.injective
  rw [he, he, hcd]

private theorem exponent_dvd_of_pow_sub_one_dvd_pow_sub_one
    {p a b : ℕ} (hp : 2 ≤ p) (h : p ^ a - 1 ∣ p ^ b - 1) : a ∣ b := by
  have hgcd : p ^ Nat.gcd a b - 1 = p ^ a - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_eq_left h]
  have hpow : p ^ Nat.gcd a b = p ^ a := by
    have hpos₁ : 0 < p ^ Nat.gcd a b := by positivity
    have hpos₂ : 0 < p ^ a := by positivity
    omega
  have : Nat.gcd a b = a := Nat.pow_right_injective hp hpow
  exact (Nat.gcd_eq_left_iff_dvd).mp this

/-! ## Prime-supported Singer orders -/

/-- Suppose the odd positive modulus `a` divides `N`, and every prime divisor
of `N` already divides `a`. Then raising `a + 1` to the odd-order enlargement
factor `N / a` is congruent to one modulo `N`.

For each prime divisor `p` of `N`, lifting the exponent gives
`v_p ((a + 1) ^ (N / a) - 1) = v_p(a) + v_p(N / a) = v_p(N)`. -/
theorem dvd_add_one_pow_div_sub_one_of_primeFactors_dvd
    {a N : ℕ} (ha : 0 < a) (hN : 0 < N) (hdiv : a ∣ N)
    (haodd : Odd a)
    (hsupp : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ a) :
    N ∣ (a + 1) ^ (N / a) - 1 := by
  have hak : a * (N / a) = N := Nat.mul_div_cancel' hdiv
  have hapos : a ≤ N := Nat.le_of_dvd hN hdiv
  have hkpos : 0 < N / a := Nat.div_pos hapos ha
  have htargetpos : 0 < (a + 1) ^ (N / a) - 1 := by
    have hbase : 1 < a + 1 := by omega
    have hpow : 1 < (a + 1) ^ (N / a) :=
      one_lt_pow₀ hbase hkpos.ne'
    omega
  rw [← Nat.factorization_le_iff_dvd hN.ne' htargetpos.ne', Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · by_cases hpN : p ∣ N
    · have hpa : p ∣ a := hsupp p hp hpN
      have hp2 : p ≠ 2 := by
        intro h
        subst p
        exact haodd.not_two_dvd_nat hpa
      have hpodd : Odd p := hp.odd_of_ne_two hp2
      have hpnext : ¬ p ∣ a + 1 := by
        intro h
        have : p ∣ 1 :=
          (Nat.dvd_add_iff_left hpa).mpr (by simpa [Nat.add_comm] using h)
        exact hp.not_dvd_one this
      have hLTE := Nat.emultiplicity_pow_sub_pow hp hpodd
        (x := a + 1) (y := 1) (by simpa using hpa) hpnext (N / a)
      have hfa : a.factorization p = multiplicity p a :=
        (Nat.multiplicity_eq_factorization hp ha.ne').symm
      have hfk : (N / a).factorization p = multiplicity p (N / a) :=
        (Nat.multiplicity_eq_factorization hp hkpos.ne').symm
      have hft : ((a + 1) ^ (N / a) - 1).factorization p =
          multiplicity p ((a + 1) ^ (N / a) - 1) :=
        (Nat.multiplicity_eq_factorization hp htargetpos.ne').symm
      have hfN : N.factorization p =
          a.factorization p + (N / a).factorization p := by
        calc
          N.factorization p = (a * (N / a)).factorization p :=
            congrArg (fun t : ℕ => t.factorization p) hak.symm
          _ = a.factorization p + (N / a).factorization p := by
            rw [Nat.factorization_mul ha.ne' hkpos.ne', Finsupp.add_apply]
      have hfinA : FiniteMultiplicity p a :=
        Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, ha⟩
      have hfinK : FiniteMultiplicity p (N / a) :=
        Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, hkpos⟩
      have hfinT : FiniteMultiplicity p ((a + 1) ^ (N / a) - 1) :=
        Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, htargetpos⟩
      have hLTE' : emultiplicity p ((a + 1) ^ (N / a) - 1) =
          emultiplicity p a + emultiplicity p (N / a) := by
        simpa using hLTE
      rw [hfinT.emultiplicity_eq_multiplicity,
        hfinA.emultiplicity_eq_multiplicity,
        hfinK.emultiplicity_eq_multiplicity] at hLTE'
      have hmul : multiplicity p ((a + 1) ^ (N / a) - 1) =
          multiplicity p a + multiplicity p (N / a) := by
        exact_mod_cast hLTE'
      rw [hfN, hfa, hfk, hft, hmul]
    · rw [Nat.factorization_eq_zero_of_not_dvd hpN]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime N hp,
      Nat.factorization_eq_zero_of_not_prime _ hp]

/-- If `N` is a period modulus for powers of two, is divisible by
`2 ^ n - 1`, and has no new prime divisors beyond `2 ^ n - 1`, then any
minimal exponent `m` for that period contains `n` with odd quotient.

The odd comparison period is `n * (N / (2 ^ n - 1))`. -/
theorem mersenne_exponent_dvd_and_odd_quotient_of_primeFactors_dvd
    {n m N : ℕ} (hn : 0 < n) (hm : 0 < m) (hN : 0 < N)
    (hbase : 2 ^ n - 1 ∣ N)
    (hsupp : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ 2 ^ n - 1)
    (hperiod : N ∣ 2 ^ m - 1)
    (hminimal : ∀ k : ℕ, N ∣ 2 ^ k - 1 → m ∣ k) :
    n ∣ m ∧ Odd (m / n) := by
  have hnm : n ∣ m :=
    exponent_dvd_of_pow_sub_one_dvd_pow_sub_one (p := 2) (by omega)
      (hbase.trans hperiod)
  let a := 2 ^ n - 1
  let k := N / a
  have ha : 0 < a := by
    dsimp [a]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have haodd : Odd a := by
    rw [Nat.odd_iff]
    simpa [a] using hn
  have hNodd : Odd N := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro htwo
    exact haodd.not_two_dvd_nat (hsupp 2 Nat.prime_two htwo)
  have hkodd : Odd k := Odd.of_dvd_nat hNodd (by
    dsimp [k]
    refine ⟨a, ?_⟩
    rw [Nat.div_mul_cancel hbase])
  have hsupported : N ∣ (a + 1) ^ k - 1 :=
    dvd_add_one_pow_div_sub_one_of_primeFactors_dvd ha hN hbase haodd (by
      intro p hp hpN
      exact hsupp p hp hpN)
  have hpow : N ∣ 2 ^ (n * k) - 1 := by
    have ha1 : a + 1 = 2 ^ n := by
      dsimp [a]
      omega
    rw [ha1] at hsupported
    simpa only [pow_mul] using hsupported
  have hm_nk : m ∣ n * k := hminimal (n * k) hpow
  have hdvd : m / n ∣ k := by
    obtain ⟨d, hd⟩ := hnm
    subst m
    have hdk : d ∣ k := (Nat.mul_dvd_mul_iff_left hn).mp hm_nk
    rw [Nat.mul_comm n d, Nat.mul_div_left d hn]
    exact hdk
  exact ⟨hnm, Odd.of_dvd_nat hkodd hdvd⟩

/-- Let `lambda` generate `GF(2 ^ m)` over `𝔽₂`. If its multiplicative
order `N` is divisible by `2 ^ n - 1` and every prime divisor of `N` divides
`2 ^ n - 1`, then `n` divides `m` with odd quotient.

The generation hypothesis identifies `m` as the minimal Frobenius period of
`lambda`; this is the finite-field form used in Higman's Lemma 11. -/
theorem galoisField_degree_dvd_and_odd_quotient_of_primeFactors_dvd
    {n m N : ℕ} (hn : 0 < n) (hm : 0 < m) (hN : 0 < N)
    (lambda : GaloisField 2 m)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set (GaloisField 2 m)) = ⊤)
    (horder : orderOf lambda = N)
    (hbase : 2 ^ n - 1 ∣ N)
    (hsupp : ∀ p : ℕ, p.Prime → p ∣ N → p ∣ 2 ^ n - 1) :
    n ∣ m ∧ Odd (m / n) := by
  let L := GaloisField 2 m
  have hlambdaNe : lambda ≠ 0 := by
    intro hzero
    subst lambda
    simp at horder
    omega
  have hperiod : N ∣ 2 ^ m - 1 := by
    haveI : Fintype L := Fintype.ofFinite L
    have hcard : Fintype.card L = 2 ^ m := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm.ne']
    have hpow : lambda ^ (2 ^ m - 1) = 1 := by
      rw [← hcard]
      exact FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hminimal : ∀ k : ℕ, N ∣ 2 ^ k - 1 → m ∣ k := by
    intro k hk
    have hlambdaPow : lambda ^ (2 ^ k) = lambda := by
      have hq : lambda ^ (2 ^ k - 1) = 1 := by
        rw [← horder] at hk
        exact orderOf_dvd_iff_pow_eq_one.mp hk
      calc
        lambda ^ (2 ^ k) = lambda ^ ((2 ^ k - 1) + 1) := by
          rw [Nat.sub_add_cancel (Nat.one_le_pow k 2 (by omega))]
        _ = lambda ^ (2 ^ k - 1) * lambda := by rw [pow_succ]
        _ = lambda := by rw [hq, one_mul]
    let sigma := FiniteField.frobeniusAlgHom (ZMod 2) L
    have hsigma : sigma ^ k = 1 := by
      apply AlgHom.ext_of_adjoin_eq_top hgen
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      dsimp [sigma, L]
      simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom,
        pow_iterate, ZMod.card, AlgHom.one_apply] using hlambdaPow
    have h := orderOf_dvd_of_pow_eq_one hsigma
    rw [FiniteField.orderOf_frobeniusAlgHom (ZMod 2) L,
      show Module.finrank (ZMod 2) L = m from GaloisField.finrank 2 hm.ne'] at h
    exact h
  exact mersenne_exponent_dvd_and_odd_quotient_of_primeFactors_dvd
    hn hm hN hbase hsupp hperiod hminimal

/-- A faithful irreducible cyclic `𝔽₂`-action and a faithful action of the
same actor which is transitive on the nonzero vectors have equal dimensions.

The transitive action makes the actor order `2 ^ n - 1`.  In the Singer field
of the irreducible action, a generator of that order generates the whole field.
Its Frobenius period gives one dimension divisibility; its multiplicative order
gives the reverse divisibility. -/
theorem finrank_eq_of_faithful_irreducible_and_faithful_transitive_nonzero
    {C V₁ V₂ : Type uGenerator}
    [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Finite V₂] [Nontrivial V₂]
    (rho₁ : Representation (ZMod 2) C V₁)
    (rho₂ : Representation (ZMod 2) C V₂)
    (hirr₁ : Representation.IsIrreducible rho₁)
    (hfaith₁ : Function.Injective rho₁)
    (hfaith₂ : Function.Injective rho₂)
    (htrans₂ : ∀ v w : V₂, v ≠ 0 → w ≠ 0 → ∃ c : C, rho₂ c v = w) :
    Module.finrank (ZMod 2) V₁ = Module.finrank (ZMod 2) V₂ := by
  classical
  letI : Representation.IsIrreducible rho₁ := hirr₁
  letI : Nontrivial V₁ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact bot_ne_top (α := Subrepresentation rho₁)
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  let m := Module.finrank (ZMod 2) V₁
  let n := Module.finrank (ZMod 2) V₂
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨c, hcgen⟩ := IsCyclic.exists_generator (α := C)
  have hcardV₂ : Nat.card V₂ = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [Nat.card_eq_fintype_card, n]
  have hcardC : Nat.card C = 2 ^ n - 1 := by
    rw [natCard_actor_eq_natCard_sub_one_of_faithful_transitive_nonzero
      (F := ZMod 2) (C := C) (V := V₂) rho₂ hfaith₂ htrans₂,
      hcardV₂]
  have hcorder : orderOf c = 2 ^ n - 1 :=
    (orderOf_eq_card_of_forall_mem_zpowers hcgen).trans hcardC
  obtain ⟨e, mu, hmu, hcompat⟩ :=
    exists_galoisFieldLinearModel_of_faithful_irreducible
      rho₁ m hm rfl hirr₁ hfaith₁
  let K := GaloisField 2 m
  let lambda : K := (mu c : K)
  have hlambdaOrder : orderOf lambda = 2 ^ n - 1 := by
    exact orderOf_units.trans ((orderOf_injective mu hmu c).trans hcorder)
  let A : Subalgebra (ZMod 2) K :=
    Algebra.adjoin (ZMod 2) ({lambda} : Set K)
  let W : Subrepresentation rho₁ :=
    { toSubmodule := A.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule := by
        intro g v hv
        change e (rho₁ g v) ∈ A
        rw [hcompat]
        apply A.mul_mem
        · have hgpow : g ∈ Submonoid.powers c := by
            exact (isOfFinOrder_of_finite c).mem_powers_iff_mem_zpowers.mpr
              (hcgen g)
          obtain ⟨k, rfl⟩ := hgpow
          change (mu (c ^ k) : K) ∈ A
          rw [map_pow]
          exact A.pow_mem
            (Algebra.self_mem_adjoin_singleton (ZMod 2) lambda) k
        · exact hv }
  have hWne : W ≠ ⊥ := by
    intro hW
    have hone : e.symm (1 : K) ∈ W := by
      change e (e.symm (1 : K)) ∈ A
      rw [e.apply_symm_apply]
      exact A.one_mem
    rw [hW] at hone
    have hzero : e.symm (1 : K) = 0 := hone
    have : (1 : K) = 0 := by
      rw [← e.apply_symm_apply (1 : K), hzero, map_zero]
    exact one_ne_zero this
  have hWtop : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hWne
  have hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : e.symm x ∈ W := by
      rw [hWtop]
      exact Submodule.mem_top
    change e (e.symm x) ∈ A at hx
    simpa [A] using hx
  have hlambdaPow : lambda ^ (2 ^ n) = lambda := by
    have hq : lambda ^ (2 ^ n - 1) = 1 := by
      rw [← hlambdaOrder]
      exact pow_orderOf_eq_one lambda
    calc
      lambda ^ (2 ^ n) = lambda ^ ((2 ^ n - 1) + 1) := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow n 2 (by omega))]
      _ = lambda ^ (2 ^ n - 1) * lambda := by rw [pow_succ]
      _ = lambda := by rw [hq, one_mul]
  let sigma := FiniteField.frobeniusAlgHom (ZMod 2) K
  have hsigma : sigma ^ n = 1 := by
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    dsimp [sigma]
    simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom,
      pow_iterate, ZMod.card, AlgHom.one_apply] using hlambdaPow
  have hm_dvd_n : m ∣ n := by
    have h := orderOf_dvd_of_pow_eq_one hsigma
    rw [FiniteField.orderOf_frobeniusAlgHom (ZMod 2) K,
      show Module.finrank (ZMod 2) K = m from GaloisField.finrank 2 hm] at h
    exact h
  have hlambdaCardPow : lambda ^ (2 ^ m - 1) = 1 := by
    have hlambdaNe : lambda ≠ 0 := Units.ne_zero (mu c)
    haveI : Fintype K := Fintype.ofFinite K
    have hcardK : Fintype.card K = 2 ^ m := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm]
    rw [← hcardK]
    exact FiniteField.pow_card_sub_one_eq_one lambda hlambdaNe
  have hq_dvd : 2 ^ n - 1 ∣ 2 ^ m - 1 := by
    rw [← hlambdaOrder]
    exact orderOf_dvd_of_pow_eq_one hlambdaCardPow
  have hn_dvd_m : n ∣ m :=
    exponent_dvd_of_pow_sub_one_dvd_pow_sub_one
      (p := 2) (by omega) hq_dvd
  exact Nat.dvd_antisymm hm_dvd_n hn_dvd_m

end OddOrder.RepresentationTheory
