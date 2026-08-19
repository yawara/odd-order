/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralGraded
import OddOrder.GroupTheory.RepresentationTheory.BaseChange
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction
import OddOrder.GroupTheory.RepresentationTheory.FrobeniusCoordinates
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Colex
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Higman — lower central spectrum: the bilinear-map layer

Split from the parent file (issue 0149, the longFile-1500 campaign); the parent
imports this leaf, so downstream imports are unchanged.
-/


set_option autoImplicit false

open Module Polynomial
open OddOrder.RepresentationTheory
open scoped BigOperators TensorProduct IsMulCommutative Fin.NatCast

namespace OddOrder.Higman.Suzuki2Groups

universe uR uK uM uN uH uX

namespace LinearMap.BilinMap

/-- Equivariance of a bilinear map survives extension of scalars. -/
theorem baseChange_equivariant
    {R : Type uR} {K : Type uK} {M : Type uM} {N : Type uN}
    [CommSemiring R] [CommSemiring K] [Algebra R K]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (b : LinearMap.BilinMap R M N) (T₁ : Module.End R M) (T₂ : Module.End R N)
    (h : ∀ x y, T₂ (b x y) = b (T₁ x) (T₁ y))
    (u v : K ⊗[R] M) :
    T₂.baseChange K (b.baseChange K u v) =
      b.baseChange K (T₁.baseChange K u) (T₁.baseChange K v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul c y => simp [h]
      | add v w hv hw => simp [hv, hw]
  | add u w hu hw => simp [hu, hw]

end LinearMap.BilinMap

/-! ## Scalar extension of the Higman bracket -/

/-- Higman's actual commutator bracket after extending scalars from `F₂` to `K`. -/
noncomputable def lowerCentralCommutatorBilinearBaseChange
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H] :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    LinearMap.BilinMap K
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
      (K ⊗[ZMod 2] Additive (lowerCentralLayer H 1)) := by
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  exact LinearMap.BilinMap.baseChange K (lowerCentralCommutatorBilinear H)

/-- The scalar-extended Higman bracket intertwines the scalar-extended
actions on the first and second lower-central layers. -/
theorem lowerCentralCommutatorBilinearBaseChange_equivariant
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (u v :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    (lowerCentralLayerRepresentation phi 1 g).baseChange K
        (lowerCentralCommutatorBilinearBaseChange K H u v) =
      lowerCentralCommutatorBilinearBaseChange K H
        ((lowerCentralLayerRepresentation phi 0 g).baseChange K u)
        ((lowerCentralLayerRepresentation phi 0 g).baseChange K v) := by
  let : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  let : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  unfold lowerCentralCommutatorBilinearBaseChange
  apply LinearMap.BilinMap.baseChange_equivariant
  intro x y
  simpa only [← lowerCentralLayerRepresentation_apply, ofMul_toMul] using
    lowerCentralCommutatorBilinear_equivariant phi g x y

/-- The bracket of two scalar-extended eigenvectors has the product
eigenvalue.  The bracket is allowed to vanish, so this is stated as the
eigenvector equation rather than `HasEigenvector`. -/
theorem lowerCentralCommutatorBilinearBaseChange_eigenweight
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    {H : Type uH} {X : Type uX} [Group H] [Group X]
    (phi : X →* MulAut H) (g : X)
    (a c : K)
    (u v :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 0))
    (hu :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      (lowerCentralLayerRepresentation phi 0 g).baseChange K u = a • u)
    (hv :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      (lowerCentralLayerRepresentation phi 0 g).baseChange K v = c • v) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    (lowerCentralLayerRepresentation phi 1 g).baseChange K
        (lowerCentralCommutatorBilinearBaseChange K H u v) =
      (a * c) • lowerCentralCommutatorBilinearBaseChange K H u v := by
  let : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  let : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  rw [lowerCentralCommutatorBilinearBaseChange_equivariant, hu, hv]
  simp [smul_smul, mul_comm]


namespace LinearMap.BilinMap

/-- In characteristic two, diagonal vanishing of a bilinear map implies
symmetry. -/
theorem zmodTwo_symmetric_of_self_eq_zero
    {M : Type uM} {N : Type uN}
    [AddCommMonoid M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (b : LinearMap.BilinMap (ZMod 2) M N)
    (hdiag : ∀ x, b x x = 0) (x y : M) :
    b x y = b y x := by
  have h := hdiag (x + y)
  rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add] at h
  simp only [hdiag, zero_add, add_zero] at h
  have hminus : (-1 : ZMod 2) = 1 := by decide
  have hneg (z : N) : -z = z := by
    rw [← neg_one_smul (ZMod 2), hminus, one_smul]
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg, hneg]
  exact h

/-- Diagonal vanishing of an `F₂`-bilinear map survives scalar extension
to a field of characteristic two. -/
theorem zmodTwo_baseChange_self_eq_zero
    {K : Type uK} [Field K] [Algebra (ZMod 2) K]
    {M : Type uM} {N : Type uN}
    [AddCommMonoid M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (b : LinearMap.BilinMap (ZMod 2) M N)
    (hdiag : ∀ x, b x x = 0) (u : K ⊗[ZMod 2] M) :
    b.baseChange K u u = 0 := by
  let : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  have hsymm : ∀ x y, b x y = b y x :=
    zmodTwo_symmetric_of_self_eq_zero b hdiag
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [hdiag]
  | add u v hu hv =>
      rw [LinearMap.map_add₂, LinearMap.map_add, LinearMap.map_add]
      simp only [hu, hv, zero_add, add_zero]
      rw [LinearMap.BilinMap.baseChange_isSymm hsymm v u]
      rw [← two_smul K]
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      rw [htwo, zero_smul]

end LinearMap.BilinMap

/-- The scalar-extended Higman commutator bracket remains alternating. -/
@[simp]
theorem lowerCentralCommutatorBilinearBaseChange_self
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H]
    (u :
      letI : IsMulCommutative (lowerCentralLayer H 0) :=
        lowerCentralLayerIsMulCommutative H 0
      letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
        lowerCentralLayerZmodModule H 0
      K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    lowerCentralCommutatorBilinearBaseChange K H u u = 0 := by
  let : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  let : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  unfold lowerCentralCommutatorBilinearBaseChange
  exact LinearMap.BilinMap.zmodTwo_baseChange_self_eq_zero
    (lowerCentralCommutatorBilinear H)
    (lowerCentralCommutatorBilinear_self H) u


namespace LinearMap.BilinMap

/-- Full spanning range of a bilinear map survives scalar extension. -/
theorem baseChange_span_eq_top
    {R : Type uR} {K : Type uK} {M : Type uM} {N : Type uN}
    [CommSemiring R] [CommSemiring K] [Algebra R K]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (b : LinearMap.BilinMap R M N)
    (hspan : Submodule.span R
      (Set.range fun z : M × M => b z.1 z.2) = ⊤) :
    Submodule.span K
      (Set.range fun z : (K ⊗[R] M) × (K ⊗[R] M) =>
        b.baseChange K z.1 z.2) = ⊤ := by
  let f : (M ⊗[R] M) →ₗ[R] N := TensorProduct.lift b
  have hsets :
      Set.image2 (fun x y => b x y)
          (↑(⊤ : Submodule R M) : Set M)
          (↑(⊤ : Submodule R M) : Set M) =
        Set.range (fun z : M × M => b z.1 z.2) := by
    ext z
    constructor
    · rintro ⟨x, _hx, y, _hy, rfl⟩
      exact ⟨(x, y), rfl⟩
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨x, Submodule.mem_top, y, Submodule.mem_top, rfl⟩
  have hmap2 : Submodule.map₂ b ⊤ ⊤ = ⊤ := by
    rw [Submodule.map₂_eq_span_image2, hsets, hspan]
  have hmapIncl :
      LinearMap.range
          (TensorProduct.mapIncl (⊤ : Submodule R M) (⊤ : Submodule R M)) = ⊤ := by
    rw [TensorProduct.range_mapIncl, TensorProduct.map₂_mk_top_top_eq_top]
  have hrange : LinearMap.range f = ⊤ := by
    rw [← LinearMap.range_comp_of_range_eq_top f hmapIncl]
    rw [← TensorProduct.map₂_eq_range_lift_comp_mapIncl, hmap2]
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
  have hsurjK : Function.Surjective (f.baseChange K) :=
    LinearMap.baseChange_surjective K hsurj
  let S : Submodule K (K ⊗[R] N) :=
    Submodule.span K
      (Set.range fun z : (K ⊗[R] M) × (K ⊗[R] M) =>
        b.baseChange K z.1 z.2)
  have hsimple (a : K) (t : M ⊗[R] M) :
      f.baseChange K (a ⊗ₜ[R] t) ∈ S := by
    induction t using TensorProduct.induction_on with
    | zero => simp [S]
    | tmul x y =>
        apply Submodule.subset_span
        refine ⟨(a ⊗ₜ[R] x, 1 ⊗ₜ[R] y), ?_⟩
        simp [f]
    | add t w ht hw =>
        rw [TensorProduct.tmul_add, map_add]
        exact S.add_mem ht hw
  apply Submodule.eq_top_iff'.mpr
  intro z
  obtain ⟨t, rfl⟩ := hsurjK z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => exact hsimple a t
  | add t w ht hw =>
      rw [map_add]
      exact S.add_mem ht hw

end LinearMap.BilinMap

/-- Scalar extension preserves the full spanning range of Higman's actual
commutator bracket. -/
theorem lowerCentralCommutatorBilinearBaseChange_span_eq_top
    (K : Type uK) [Field K] [Algebra (ZMod 2) K]
    (H : Type uH) [Group H] :
    letI : IsMulCommutative (lowerCentralLayer H 0) :=
      lowerCentralLayerIsMulCommutative H 0
    letI : IsMulCommutative (lowerCentralLayer H 1) :=
      lowerCentralLayerIsMulCommutative H 1
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
      lowerCentralLayerZmodModule H 0
    letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
      lowerCentralLayerZmodModule H 1
    Submodule.span K
      (Set.range fun z :
          (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) ×
            (K ⊗[ZMod 2] Additive (lowerCentralLayer H 0)) =>
        lowerCentralCommutatorBilinearBaseChange K H z.1 z.2) = ⊤ := by
  let : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  let : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  let : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
    lowerCentralLayerZmodModule H 1
  unfold lowerCentralCommutatorBilinearBaseChange
  exact LinearMap.BilinMap.baseChange_span_eq_top
    (lowerCentralCommutatorBilinear H)
    (lowerCentralCommutatorBilinear_span_eq_top H)



/-! ## Frobenius eigenbases -/

universe uEigenF uEigenK uEigenV

/-- If an endomorphism is conjugate to left multiplication by a field generator,
its characteristic polynomial is the generator's minimal polynomial. -/
theorem charpoly_eq_minpoly_of_conj_lmul
    {F : Type uEigenF} {K : Type uEigenK} {V : Type uEigenV}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (T : Module.End F V) (e : V ≃ₗ[F] K) (lambda : K)
    (hconj : e.conj T = Algebra.lmul F K lambda)
    (hgen : Algebra.adjoin F ({lambda} : Set K) = ⊤) :
    T.charpoly = minpoly F lambda := by
  let pb : PowerBasis F K :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral lambda) hgen
  calc
    T.charpoly = (e.conj T).charpoly := (e.charpoly_conj T).symm
    _ = (Algebra.lmul F K lambda).charpoly := congrArg LinearMap.charpoly hconj
    _ = (Algebra.leftMulMatrix pb.basis lambda).charpoly := by
      rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
    _ = minpoly F lambda := by
      simpa [pb, PowerBasis.ofAdjoinEqTop_gen] using charpoly_leftMulMatrix pb


/-- A field generator has a full Frobenius orbit, so a linear operator whose
characteristic polynomial is its minimal polynomial admits the Frobenius
conjugates as a full eigenbasis after scalar extension. No multiplicative
primitive-root hypothesis is used. -/
theorem exists_frobeniusEigenbasis_of_generator_and_charpoly
    {K : Type uEigenK} {V : Type uEigenV}
    [Field K] [Finite K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (T : Module.End (ZMod 2) V)
    (m : ℕ)
    (hfinK : Module.finrank (ZMod 2) K = m)
    (lambda : K)
    (hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set K) = ⊤)
    (hchar : T.charpoly = minpoly (ZMod 2) lambda) :
    ∃ b : Basis (Fin m) K (K ⊗[ZMod 2] V), ∀ i,
      T.baseChange K (b i) = lambda ^ (2 ^ i.val) • b i := by
  let weight : Fin m → K := fun i ↦ lambda ^ (2 ^ i.val)
  let TK : Module.End K (K ⊗[ZMod 2] V) := T.baseChange K
  have hroot (i : Fin m) : TK.charpoly.IsRoot (weight i) := by
    change (T.baseChange K).charpoly.IsRoot (weight i)
    rw [LinearMap.charpoly_baseChange, hchar]
    let σ : K →ₐ[ZMod 2] K :=
      FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val
    have hσ : σ lambda = weight i := by
      simp [σ, weight, AlgHom.coe_pow,
        FiniteField.coe_frobeniusAlgHom, pow_iterate]
    rw [Polynomial.IsRoot, eval_map_algebraMap, ← hσ,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have heig (i : Fin m) : TK.HasEigenvalue (weight i) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hroot i
  let v : Fin m → K ⊗[ZMod 2] V :=
    fun i ↦ (heig i).exists_hasEigenvector.choose
  have hv (i : Fin m) : TK.HasEigenvector (weight i) (v i) :=
    (heig i).exists_hasEigenvector.choose_spec
  have hfrob : Function.Injective
      (fun i : Fin m ↦
        FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val) := by
    intro i j hij
    have hcast : Fin.cast hfinK.symm i = Fin.cast hfinK.symm j := by
      apply (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) K).1
      simpa using hij
    exact Fin.cast_injective hfinK.symm hcast
  have hweight : Function.Injective weight := by
    intro i j hij
    apply hfrob
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    have hx' : x = lambda := Set.mem_singleton_iff.mp hx
    subst x
    simpa [weight, AlgHom.coe_pow,
      FiniteField.coe_frobeniusAlgHom, pow_iterate] using hij
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' TK weight hweight v hv
  let pb : PowerBasis (ZMod 2) K :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral lambda) hgen
  have hminDegree : (minpoly (ZMod 2) lambda).natDegree = m := by
    calc
      (minpoly (ZMod 2) lambda).natDegree = pb.dim := by
        simp [pb]
      _ = Module.finrank (ZMod 2) K := (pb.finrank).symm
      _ = m := hfinK
  have hfinV : Module.finrank (ZMod 2) V = m := by
    rw [← T.charpoly_natDegree, hchar, hminDegree]
  have hcard : Fintype.card (Fin m) =
      Module.finrank K (K ⊗[ZMod 2] V) := by
    rw [Fintype.card_fin, Module.finrank_baseChange, hfinV]
  let b : Basis (Fin m) K (K ⊗[ZMod 2] V) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  refine ⟨b, fun i ↦ ?_⟩
  have hb : b i = v i := by
    change basisOfLinearIndependentOfCardEqFinrank' v hli hcard i = v i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rw [hb]
  exact (hv i).apply_eq_smul


/-- If an `F₂`-endomorphism has the minimal polynomial of a primitive element of a finite
splitting field `K` as characteristic polynomial, scalar extension to `K` has the Frobenius
conjugates as a full eigenbasis. -/
theorem exists_frobeniusEigenbasis_of_charpoly_eq_minpoly
    {K : Type uEigenK} {V : Type uEigenV} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (T : Module.End (ZMod 2) V) (n : ℕ) (_hn : 2 ≤ n) (lambda : K)
    (hfin : Module.finrank (ZMod 2) V = n)
    (hchar : T.charpoly = minpoly (ZMod 2) lambda)
    (hprim : IsPrimitiveRoot lambda (2 ^ n - 1)) :
    ∃ b : Basis (Fin n) K (K ⊗[ZMod 2] V), ∀ i,
      T.baseChange K (b i) = lambda ^ (2 ^ i.val) • b i := by
  let weight : Fin n → K := fun i ↦ lambda ^ (2 ^ i.val)
  let TK : Module.End K (K ⊗[ZMod 2] V) := T.baseChange K
  have hroot (i : Fin n) :
      TK.charpoly.IsRoot (weight i) := by
    change (T.baseChange K).charpoly.IsRoot (weight i)
    rw [LinearMap.charpoly_baseChange, hchar]
    let σ : K →ₐ[ZMod 2] K := FiniteField.frobeniusAlgHom (ZMod 2) K ^ i.val
    have hσ : σ lambda = weight i := by
      simp [σ, weight, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
    rw [Polynomial.IsRoot, eval_map_algebraMap, ← hσ,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have heig (i : Fin n) : TK.HasEigenvalue (weight i) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact hroot i
  let v : Fin n → K ⊗[ZMod 2] V := fun i ↦ (heig i).exists_hasEigenvector.choose
  have hv (i : Fin n) : TK.HasEigenvector (weight i) (v i) :=
    (heig i).exists_hasEigenvector.choose_spec
  have hweight : Function.Injective weight := by
    intro i j hij
    have hn_half_two : 2 ≤ 2 ^ (n - 1) := by
      calc
        2 = 2 ^ 1 := by simp
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hi_lt : 2 ^ i.val < 2 ^ n - 1 := by
      have hi_half : 2 ^ i.val ≤ 2 ^ (n - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hn_pow : 2 ^ (n - 1) < 2 ^ n - 1 := by
        have heq : 2 ^ n = 2 ^ (n - 1) * 2 := by
          calc
            2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
            _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        omega
      omega
    have hj_lt : 2 ^ j.val < 2 ^ n - 1 := by
      have hj_half : 2 ^ j.val ≤ 2 ^ (n - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hn_pow : 2 ^ (n - 1) < 2 ^ n - 1 := by
        have heq : 2 ^ n = 2 ^ (n - 1) * 2 := by
          calc
            2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
            _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
        omega
      omega
    apply Fin.ext
    exact (Nat.pow_right_injective (by omega : 1 < 2))
      (hprim.pow_inj hi_lt hj_lt hij)
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' TK weight hweight v hv
  have hcard : Fintype.card (Fin n) = Module.finrank K (K ⊗[ZMod 2] V) := by
    rw [Fintype.card_fin, Module.finrank_baseChange, hfin]
  let b : Basis (Fin n) K (K ⊗[ZMod 2] V) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  refine ⟨b, fun i ↦ ?_⟩
  have hb : b i = v i := by
    change basisOfLinearIndependentOfCardEqFinrank' v hli hcard i = v i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  rw [hb]
  exact (hv i).apply_eq_smul


/-! ## Singer field model -/

universe uSinger uSingerF uSingerC uSingerV


end OddOrder.Higman.Suzuki2Groups
