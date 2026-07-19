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
# Higman's lower-central spectral argument

G. Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 4,
pp. 84--85; used in Peterfalvi, Appendix III.

This coherent spectral topic extends the actual lower-central commutator bracket
from `F₂` to a splitting field, proves its alternating, equivariant, and
full-span properties survive scalar extension, constructs the Frobenius
conjugate eigenbasis supplied by a Singer field model, and isolates the final
primitive-root contradiction. Together these are the representation-theoretic
infrastructure for Higman's proof that the first two lower-central layers are
not isomorphic under the given automorphism.
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
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
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
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
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
  letI : CharP K 2 :=
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
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
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
  letI : IsMulCommutative (lowerCentralLayer H 0) :=
    lowerCentralLayerIsMulCommutative H 0
  letI : IsMulCommutative (lowerCentralLayer H 1) :=
    lowerCentralLayerIsMulCommutative H 1
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 0)) :=
    lowerCentralLayerZmodModule H 0
  letI : Module (ZMod 2) (Additive (lowerCentralLayer H 1)) :=
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

/-- A transitive action on the nonzero vectors is irreducible. -/
theorem representation_isIrreducible_of_transitive_nonzero
    {F : Type uSingerF} {C : Type uSingerC} {V : Type uSingerV}
    [Field F] [Group C] [AddCommGroup V] [Module F V]
    (rho : Representation F C V) [Nontrivial V]
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ c : C, rho c v = w) :
    Representation.IsIrreducible rho := by
  have hbot_ne_top : (⊥ : Subrepresentation rho) ≠ ⊤ := fun h =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  letI : Nontrivial (Subrepresentation rho) := ⟨⊥, ⊤, hbot_ne_top⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hWbot
  apply Subrepresentation.toSubmodule_injective
  change W.toSubmodule = ⊤
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · subst w
    exact W.toSubmodule.zero_mem
  · have hne : ∃ v : V, v ∈ W ∧ v ≠ 0 := by
      by_contra h
      apply hWbot
      apply Subrepresentation.toSubmodule_injective
      change W.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro v hv
      by_contra hv0
      exact h ⟨v, hv, hv0⟩
    obtain ⟨v, hvW, hv0⟩ := hne
    obtain ⟨c, hc⟩ := htrans v w hv0 hw
    rw [← hc]
    exact W.apply_mem_toSubmodule c hvW

/-- The Singer field model for a faithful irreducible action generated by an
element of full Singer order. -/
theorem exists_singerEigenmodel_of_faithful_irreducible
    {C V : Type uSinger} [CommGroup C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (rho : Representation (ZMod 2) C V)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin : Module.finrank (ZMod 2) V = n)
    (hirr : Representation.IsIrreducible rho)
    (hfaith : Function.Injective rho)
    (c : C) (hc : orderOf c = 2 ^ n - 1) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 n) (lambda : GaloisField 2 n),
      IsPrimitiveRoot lambda (2 ^ n - 1) ∧
      e.conj (rho c) = Algebra.lmul (ZMod 2) (GaloisField 2 n) lambda ∧
      Algebra.adjoin (ZMod 2) ({lambda} : Set (GaloisField 2 n)) = ⊤ := by
  classical
  have hn0 : n ≠ 0 := by omega
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  letI : Module (MonoidAlgebra (ZMod 2) C) V :=
    Module.compHom V (rho.asAlgebraHom).toRingHom
  have hsmul : ∀ (g : C) (v : V),
      MonoidAlgebra.of (ZMod 2) C g • v = rho g v := by
    intro g v
    change rho.asAlgebraHom (MonoidAlgebra.of (ZMod 2) C g) v = rho g v
    rw [Representation.asAlgebraHom_of]
  haveI : IsSimpleModule (MonoidAlgebra (ZMod 2) C) V :=
    (Representation.irreducible_iff_isSimpleModule_asModule rho).mp hirr
  have hfaith' : ∀ g : C,
      (∀ v : V, MonoidAlgebra.of (ZMod 2) C g • v = v) → g = 1 := by
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
      (p := 2) (C := C) (M := V) hn0 hcardV hfaith'
  let e : V ≃ₗ[ZMod 2] GaloisField 2 n :=
    { e0 with map_smul' := ZMod.map_smul e0.toAddMonoidHom }
  let lambda : GaloisField 2 n := (mu c : GaloisField 2 n)
  have hlambdaOrder : orderOf lambda = 2 ^ n - 1 := by
    exact orderOf_units.trans ((orderOf_injective mu hmu c).trans hc)
  have hprim : IsPrimitiveRoot lambda (2 ^ n - 1) :=
    IsPrimitiveRoot.iff_orderOf.mpr hlambdaOrder
  have hconj :
      e.conj (rho c) = Algebra.lmul (ZMod 2) (GaloisField 2 n) lambda := by
    ext x
    rw [LinearEquiv.conj_apply_apply]
    change e0 (rho c (e.symm x)) = lambda * x
    rw [← hsmul c (e.symm x), hcompat]
    rw [show e0 (e.symm x) = x from e.apply_symm_apply x]
  have hN : 2 ^ n - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hn0 (by omega))
  letI : NeZero (2 ^ n - 1) := ⟨hN⟩
  have hcardK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcardKf : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, hcardK]
  have hgen : Algebra.adjoin (ZMod 2) ({lambda} : Set (GaloisField 2 n)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 0
    · subst x
      exact (Algebra.adjoin (ZMod 2)
        ({lambda} : Set (GaloisField 2 n))).zero_mem
    · have hxpow : x ^ (2 ^ n - 1) = 1 := by
        rw [← hcardKf]
        exact FiniteField.pow_card_sub_one_eq_one x hx
      obtain ⟨i, _hi, hi⟩ := hprim.eq_pow_of_pow_eq_one hxpow
      rw [← hi]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton (ZMod 2) lambda) i
  exact ⟨e, lambda, hprim, hconj, hgen⟩


/-- The Singer field model feeds the Frobenius eigenbasis construction. -/
theorem exists_singerFrobeniusEigenbasis_of_faithful_irreducible
    {C V : Type uSinger} [CommGroup C] [Finite C]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (rho : Representation (ZMod 2) C V)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin : Module.finrank (ZMod 2) V = n)
    (hirr : Representation.IsIrreducible rho)
    (hfaith : Function.Injective rho)
    (c : C) (hc : orderOf c = 2 ^ n - 1) :
    ∃ (e : V ≃ₗ[ZMod 2] GaloisField 2 n) (lambda : GaloisField 2 n)
      (b : Basis (Fin n) (GaloisField 2 n)
        (GaloisField 2 n ⊗[ZMod 2] V)),
      IsPrimitiveRoot lambda (2 ^ n - 1) ∧
      e.conj (rho c) = Algebra.lmul (ZMod 2) (GaloisField 2 n) lambda ∧
      Algebra.adjoin (ZMod 2) ({lambda} : Set (GaloisField 2 n)) = ⊤ ∧
      ∀ i, (rho c).baseChange (GaloisField 2 n) (b i) =
        lambda ^ (2 ^ i.val) • b i := by
  obtain ⟨e, lambda, hprim, hconj, hgen⟩ :=
    exists_singerEigenmodel_of_faithful_irreducible
      rho n hn hfin hirr hfaith c hc
  have hchar : (rho c).charpoly = minpoly (ZMod 2) lambda :=
    charpoly_eq_minpoly_of_conj_lmul (rho c) e lambda hconj hgen
  obtain ⟨b, hb⟩ := exists_frobeniusEigenbasis_of_charpoly_eq_minpoly
    (rho c) n hn lambda hfin hchar hprim
  exact ⟨e, lambda, b, hprim, hconj, hgen, hb⟩


/-! ## Primitive-root contradiction -/

universe uSpectrumF uSpectrumV

/-- Unordered pairs of distinct Frobenius exponents. -/
abbrev HigmanExponentPair (n : ℕ) := {p : Fin n × Fin n // p.1.1 < p.2.1}

/-! ## Three-versus-two binary weights -/

/-- A sum of three distinct binary digits cannot equal a sum of two
distinct binary digits. -/
theorem three_distinct_twoPowers_ne_two_distinct_twoPowers
    {i j k a b : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hab : a ≠ b) :
    2 ^ i + 2 ^ j + 2 ^ k ≠ 2 ^ a + 2 ^ b := by
  intro h
  let S : Finset ℕ := {i, j, k}
  let T : Finset ℕ := {a, b}
  have hSsum : (∑ x ∈ S, 2 ^ x) = 2 ^ i + 2 ^ j + 2 ^ k := by
    simp [S, hij, hik, hjk, add_assoc]
  have hTsum : (∑ x ∈ T, 2 ^ x) = 2 ^ a + 2 ^ b := by
    simp [T, hab]
  have hST : S = T := by
    apply Finset.geomSum_injective (n := 2) (by omega)
    change (∑ x ∈ S, 2 ^ x) = ∑ x ∈ T, 2 ^ x
    rw [hSsum, hTsum, h]
  have hcard := congrArg Finset.card hST
  have hScard : S.card = 3 := by
    simp [S, hij, hik, hjk]
  have hTcard : T.card = 2 := by
    simp [T, hab]
  omega

/-- Three distinct Frobenius exponents never give a pair weight modulo
`2^n - 1`.  This is the binary-weight exclusion used after the odd-dimension
reduction in Higman's Lemma 6. -/
theorem three_distinct_frobeniusWeight_not_modEq_pairWeight
    {n : ℕ}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : HigmanExponentPair n) :
    ¬ Nat.ModEq (2 ^ n - 1)
      (2 ^ i.val + 2 ^ j.val + 2 ^ k.val)
      (2 ^ p.1.1.val + 2 ^ p.1.2.val) := by
  let S : Finset ℕ := {i.val, j.val, k.val}
  let R : Finset ℕ := Finset.range n
  have hSsub : S ⊆ R := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_range.mpr i.isLt
    · exact Finset.mem_range.mpr j.isLt
    · exact Finset.mem_range.mpr k.isLt
  have hSsum : (∑ x ∈ S, 2 ^ x) =
      2 ^ i.val + 2 ^ j.val + 2 ^ k.val := by
    have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have hjkv : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    simp [S, hijv, hikv, hjkv, add_assoc]
  have hthree_le :
      2 ^ i.val + 2 ^ j.val + 2 ^ k.val ≤ 2 ^ n - 1 := by
    rw [← hSsum]
    calc
      (∑ x ∈ S, 2 ^ x) ≤ ∑ x ∈ R, 2 ^ x :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => by positivity)
      _ = 2 ^ n - 1 := by
        simpa [R] using (Nat.geomSum_eq (m := 2) (by omega) n)
  have hpair_le :
      2 ^ p.1.1.val + 2 ^ p.1.2.val ≤ 2 ^ n - 1 := by
    let T : Finset ℕ := {p.1.1.val, p.1.2.val}
    have hTsub : T ⊆ R := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_range.mpr p.1.1.isLt
      · exact Finset.mem_range.mpr p.1.2.isLt
    have hpne : p.1.1.val ≠ p.1.2.val := by omega
    have hTsum : (∑ x ∈ T, 2 ^ x) =
        2 ^ p.1.1.val + 2 ^ p.1.2.val := by
      simp [T, hpne]
    rw [← hTsum]
    calc
      (∑ x ∈ T, 2 ^ x) ≤ ∑ x ∈ R, 2 ^ x :=
        Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => by positivity)
      _ = 2 ^ n - 1 := by
        simpa [R] using (Nat.geomSum_eq (m := 2) (by omega) n)
  have hthree_pos : 0 < 2 ^ i.val + 2 ^ j.val + 2 ^ k.val := by positivity
  have hpair_pos : 0 < 2 ^ p.1.1.val + 2 ^ p.1.2.val := by positivity
  intro hmod
  have hle : 2 ^ i.val + 2 ^ j.val + 2 ^ k.val ≤
      2 ^ p.1.1.val + 2 ^ p.1.2.val := by
    apply hmod.le_of_lt_add
    omega
  have hge : 2 ^ p.1.1.val + 2 ^ p.1.2.val ≤
      2 ^ i.val + 2 ^ j.val + 2 ^ k.val := by
    apply hmod.symm.le_of_lt_add
    omega
  have heq : 2 ^ i.val + 2 ^ j.val + 2 ^ k.val =
      2 ^ p.1.1.val + 2 ^ p.1.2.val := Nat.le_antisymm hle hge
  exact three_distinct_twoPowers_ne_two_distinct_twoPowers
    (fun h => hij (Fin.ext h))
    (fun h => hik (Fin.ext h))
    (fun h => hjk (Fin.ext h))
    (by omega) heq

/-- Primitive-root form of the three-versus-two binary-weight exclusion:
an eigenvalue attached to three distinct Frobenius exponents cannot be an
eigenvalue attached to an unordered pair. -/
theorem primitiveRoot_threeDistinctWeight_ne_pairWeight
    {F : Type*} [Field F] {n : ℕ} (hn : 3 ≤ n)
    (lambda : F) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : HigmanExponentPair n) :
    lambda ^ (2 ^ i.val + 2 ^ j.val + 2 ^ k.val) ≠
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val) := by
  intro heq
  have hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ i.val + 2 ^ j.val + 2 ^ k.val)
      (2 ^ p.1.1.val + 2 ^ p.1.2.val) := by
    have hfinite : IsOfFinOrder lambda :=
      hprim.isOfFinOrder (Nat.sub_ne_zero_of_lt
        (Nat.one_lt_pow (by omega : n ≠ 0) (by omega)))
    have h := hfinite.pow_eq_pow_iff_modEq.mp heq
    rwa [← hprim.eq_orderOf] at h
  exact three_distinct_frobeniusWeight_not_modEq_pairWeight
    i j k hij hik hjk p hmod

/-- If an operator is spanned by Higman's pair-weight eigenspaces, then the
eigenspace of a three-distinct-exponent weight is zero. -/
theorem primitiveRoot_threeDistinctWeight_eigenspace_eq_bot
    {F : Type*} {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {n : ℕ} (hn : 3 ≤ n)
    (lambda : F) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (T : Module.End F V)
    (hspan : ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n ↦
        lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)), T.eigenspace mu = ⊤)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    T.eigenspace (lambda ^ (2 ^ i.val + 2 ^ j.val + 2 ^ k.val)) = ⊥ := by
  have hnot : lambda ^ (2 ^ i.val + 2 ^ j.val + 2 ^ k.val) ∉
      Set.range (fun p : HigmanExponentPair n ↦
        lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) := by
    rintro ⟨p, hp⟩
    exact primitiveRoot_threeDistinctWeight_ne_pairWeight
      hn lambda hprim i j k hij hik hjk p hp.symm
  have hd := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup hnot
  rwa [hspan, disjoint_top] at hd

/-! ## Repeated-index binary weights -/

/-- The oriented cyclic gap from `i` to `j` in Higman's Frobenius index
cycle. -/
def higmanCyclicGap {n : ℕ} [NeZero n] (i j : Fin n) : ZMod n :=
  ZMod.finEquiv n j - ZMod.finEquiv n i

/-- The unordered pair `{i,j}` has one of Higman's two cyclic gaps `±r`. -/
def HasHigmanPairGap {n : ℕ} [NeZero n]
    (r : ZMod n) (i j : Fin n) : Prop :=
  higmanCyclicGap i j = r ∨ higmanCyclicGap i j = -r

theorem HasHigmanPairGap.comm
    {n : ℕ} [NeZero n] {r : ZMod n} {i j : Fin n} :
    HasHigmanPairGap r i j ↔ HasHigmanPairGap r j i := by
  have hneg : higmanCyclicGap j i = -higmanCyclicGap i j := by
    simp only [higmanCyclicGap]
    ring
  constructor
  · rintro (h | h)
    · right
      rw [hneg, h]
    · left
      rw [hneg, h, neg_neg]
  · rintro (h | h)
    · right
      rw [← neg_eq_iff_eq_neg, ← hneg, h]
    · left
      apply neg_injective
      rw [← hneg, h]

/-- The next Frobenius index, with indices read cyclically modulo `n`. -/
private def cyclicSuccIndex {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

private theorem twoPowers_sum_le_modulus
    {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    2 ^ a.val + 2 ^ b.val ≤ 2 ^ n - 1 := by
  let S : Finset ℕ := {a.val, b.val}
  let R : Finset ℕ := Finset.range n
  have hSsub : S ⊆ R := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_range.mpr a.isLt
    · exact Finset.mem_range.mpr b.isLt
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hSsum : (∑ x ∈ S, 2 ^ x) = 2 ^ a.val + 2 ^ b.val := by
    simp [S, habv]
  rw [← hSsum]
  calc
    (∑ x ∈ S, 2 ^ x) ≤ ∑ x ∈ R, 2 ^ x :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => by positivity)
    _ = 2 ^ n - 1 := by
      simpa [R] using (Nat.geomSum_eq (m := 2) (by omega) n)

private theorem onePower_le_modulus
    {n : ℕ} (_hn : 2 ≤ n) (a : Fin n) :
    2 ^ a.val ≤ 2 ^ n - 1 := by
  let S : Finset ℕ := {a.val}
  let R : Finset ℕ := Finset.range n
  have hSsub : S ⊆ R := by
    intro x hx
    have hx' : x = a.val := by
      simpa only [S, Finset.mem_singleton] using hx
    exact Finset.mem_range.mpr (hx' ▸ a.isLt)
  have hSsum : (∑ x ∈ S, 2 ^ x) = 2 ^ a.val := by simp [S]
  rw [← hSsum]
  calc
    (∑ x ∈ S, 2 ^ x) ≤ ∑ x ∈ R, 2 ^ x :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => by positivity)
    _ = 2 ^ n - 1 := by
      simpa [R] using (Nat.geomSum_eq (m := 2) (by omega) n)

private theorem twoDistinctPowers_eq_twoDistinctPowers_candidates
    {a b i j : ℕ} (hab : a ≠ b) (hij : i ≠ j)
    (h : 2 ^ a + 2 ^ b = 2 ^ i + 2 ^ j) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  let S : Finset ℕ := {a, b}
  let T : Finset ℕ := {i, j}
  have hSsum : (∑ x ∈ S, 2 ^ x) = 2 ^ a + 2 ^ b := by
    simp [S, hab]
  have hTsum : (∑ x ∈ T, 2 ^ x) = 2 ^ i + 2 ^ j := by
    simp [T, hij]
  have hST : S = T := by
    apply Finset.geomSum_injective (n := 2) (by omega)
    change (∑ x ∈ S, 2 ^ x) = ∑ x ∈ T, 2 ^ x
    rw [hSsum, hTsum, h]
  have haT : a ∈ T := by rw [← hST]; simp [S]
  have hbT : b ∈ T := by rw [← hST]; simp [S]
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at haT hbT
  rcases haT with hai | haj <;> rcases hbT with hbi | hbj
  · exact (hab (hai.trans hbi.symm)).elim
  · exact Or.inl ⟨hai, hbj⟩
  · exact Or.inr ⟨haj, hbi⟩
  · exact (hab (haj.trans hbj.symm)).elim

private theorem onePower_ne_twoDistinctPowers
    {a i j : ℕ} (hij : i ≠ j) :
    2 ^ a ≠ 2 ^ i + 2 ^ j := by
  intro h
  let S : Finset ℕ := {a}
  let T : Finset ℕ := {i, j}
  have hSsum : (∑ x ∈ S, 2 ^ x) = 2 ^ a := by simp [S]
  have hTsum : (∑ x ∈ T, 2 ^ x) = 2 ^ i + 2 ^ j := by
    simp [T, hij]
  have hST : S = T := by
    apply Finset.geomSum_injective (n := 2) (by omega)
    change (∑ x ∈ S, 2 ^ x) = ∑ x ∈ T, 2 ^ x
    rw [hSsum, hTsum, h]
  have hcard := congrArg Finset.card hST
  simp [S, T, hij] at hcard

/-- Doubling a binary Frobenius digit advances its index cyclically modulo
`2^n - 1`. -/
private theorem double_twoPower_modEq_cyclicSucc
    {n : ℕ} (hn : 2 ≤ n) (b : Fin n) :
    Nat.ModEq (2 ^ n - 1) (2 ^ b.val + 2 ^ b.val)
      (2 ^ (cyclicSuccIndex (by omega) b).val) := by
  let c := cyclicSuccIndex (by omega : 0 < n) b
  have hpow : 2 ^ b.val + 2 ^ b.val = 2 ^ (b.val + 1) := by
    rw [pow_succ]
    omega
  by_cases hlt : b.val + 1 < n
  · have hc : c.val = b.val + 1 := by
      simp [c, cyclicSuccIndex, Nat.mod_eq_of_lt hlt]
    rw [hpow, hc]
  · have hbn : b.val + 1 = n := by omega
    have hc : c.val = 0 := by simp [c, cyclicSuccIndex, hbn]
    rw [hpow, hbn, hc, pow_zero]
    have hpowpos : 0 < 2 ^ n := by positivity
    convert (Nat.ModEq.modulus_mul_add
      (m := 2 ^ n - 1) (a := 1) (b := 1)) using 1
    all_goals omega

private theorem normalizedTwoPower_modEq_pairWeight_candidates
    {n : ℕ} (hn : 2 ≤ n) (a c : Fin n) (p : HigmanExponentPair n)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ a.val + 2 ^ c.val)
      (2 ^ p.1.1.val + 2 ^ p.1.2.val)) :
    (a = p.1.1 ∧ c = p.1.2) ∨
      (a = p.1.2 ∧ c = p.1.1) := by
  by_cases hac : a = c
  · subst c
    let d := cyclicSuccIndex (by omega : 0 < n) a
    have hsingle : Nat.ModEq (2 ^ n - 1)
        (2 ^ d.val) (2 ^ p.1.1.val + 2 ^ p.1.2.val) :=
      (double_twoPower_modEq_cyclicSucc hn a).symm.trans hmod
    have hsingle_le := onePower_le_modulus hn d
    have hpair_le := twoPowers_sum_le_modulus p.1.1 p.1.2 (by omega)
    have hsingle_pos : 0 < 2 ^ d.val := by positivity
    have hpair_pos : 0 < 2 ^ p.1.1.val + 2 ^ p.1.2.val := by positivity
    have hle : 2 ^ d.val ≤ 2 ^ p.1.1.val + 2 ^ p.1.2.val := by
      apply hsingle.le_of_lt_add
      omega
    have hge : 2 ^ p.1.1.val + 2 ^ p.1.2.val ≤ 2 ^ d.val := by
      apply hsingle.symm.le_of_lt_add
      omega
    exact (onePower_ne_twoDistinctPowers (by omega)
      (Nat.le_antisymm hle hge)).elim
  · have hleft_le := twoPowers_sum_le_modulus a c hac
    have hright_le := twoPowers_sum_le_modulus p.1.1 p.1.2 (by omega)
    have hleft_pos : 0 < 2 ^ a.val + 2 ^ c.val := by positivity
    have hright_pos : 0 < 2 ^ p.1.1.val + 2 ^ p.1.2.val := by positivity
    have hle : 2 ^ a.val + 2 ^ c.val ≤
        2 ^ p.1.1.val + 2 ^ p.1.2.val := by
      apply hmod.le_of_lt_add
      omega
    have hge : 2 ^ p.1.1.val + 2 ^ p.1.2.val ≤
        2 ^ a.val + 2 ^ c.val := by
      apply hmod.symm.le_of_lt_add
      omega
    have heq : 2 ^ a.val + 2 ^ c.val =
        2 ^ p.1.1.val + 2 ^ p.1.2.val := Nat.le_antisymm hle hge
    rcases twoDistinctPowers_eq_twoDistinctPowers_candidates
        (fun h => hac (Fin.ext h)) (by omega) heq with h | h
    · exact Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩
    · exact Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩

private theorem finEquiv_eq_natCast
    {n : ℕ} [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      change i = (i.val : Fin (n + 1))
      apply Fin.ext
      simp

private theorem zmodSucc_eq_finPred
    {n : ℕ} [NeZero n] (b j : Fin n)
    (h : ((b.val + 1 : ℕ) : ZMod n) = (j.val : ZMod n)) :
    b = j - 1 := by
  apply (ZMod.finEquiv n).injective
  rw [map_sub]
  apply eq_sub_of_add_eq
  rw [map_one, finEquiv_eq_natCast b, finEquiv_eq_natCast j]
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- **Higman Lemma 6 (p. 86), repeated-index candidates.**

If the weight of `[[u_a,u_b],u_b]` is one of Higman's pair weights, then,
cyclically modulo `n`, its indices are `(i,j-1,j-1)` or
`(j,i-1,i-1)` for that pair `i < j`. -/
theorem repeated_frobeniusWeight_pairWeight_candidates
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (a b : Fin n) (p : HigmanExponentPair n)
    (hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ a.val + 2 ^ b.val + 2 ^ b.val)
      (2 ^ p.1.1.val + 2 ^ p.1.2.val)) :
    (a = p.1.1 ∧ b = p.1.2 - 1) ∨
      (a = p.1.2 ∧ b = p.1.1 - 1) := by
  let c := cyclicSuccIndex (by omega : 0 < n) b
  have hdouble := double_twoPower_modEq_cyclicSucc hn b
  have hnormalized : Nat.ModEq (2 ^ n - 1)
      (2 ^ a.val + 2 ^ c.val)
      (2 ^ p.1.1.val + 2 ^ p.1.2.val) := by
    have hraw : Nat.ModEq (2 ^ n - 1)
        (2 ^ a.val + 2 ^ b.val + 2 ^ b.val)
        (2 ^ a.val + 2 ^ c.val) := by
      simpa only [add_assoc] using Nat.ModEq.rfl.add hdouble
    exact hraw.symm.trans hmod
  have hcastSucc : ((b.val + 1 : ℕ) : ZMod n) = (c.val : ZMod n) := by
    change ((b.val + 1 : ℕ) : ZMod n) =
      (((b.val + 1) % n : ℕ) : ZMod n)
    exact (ZMod.natCast_mod _ _).symm
  rcases normalizedTwoPower_modEq_pairWeight_candidates hn a c p hnormalized with h | h
  · left
    constructor
    · exact h.1
    · apply zmodSucc_eq_finPred
      rw [hcastSucc, h.2]
  · right
    constructor
    · exact h.1
    · apply zmodSucc_eq_finPred
      rw [hcastSucc, h.2]

/-- Pair weights attached to distinct increasing Frobenius-index pairs are
distinct for a primitive Singer root. -/
theorem primitiveRoot_pairWeight_injective
    {F : Type*} [Field F] {n : ℕ} (hn : 2 ≤ n)
    (lambda : F) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1)) :
    Function.Injective (fun p : HigmanExponentPair n =>
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)) := by
  intro p q hpq
  have hfinite : IsOfFinOrder lambda :=
    hprim.isOfFinOrder (Nat.sub_ne_zero_of_lt
      (Nat.one_lt_pow (by omega : n ≠ 0) (by omega)))
  have hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ p.1.1.val + 2 ^ p.1.2.val)
      (2 ^ q.1.1.val + 2 ^ q.1.2.val) := by
    have h := hfinite.pow_eq_pow_iff_modEq.mp hpq
    rwa [← hprim.eq_orderOf] at h
  rcases normalizedTwoPower_modEq_pairWeight_candidates
      hn p.1.1 p.1.2 q hmod with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · exact (by omega : False).elim

/-- Equality of two binary pair weights for a primitive Singer root identifies
the two index pairs up to order. The second pair is assumed distinct; the
conclusion in particular excludes a repeated first pair. -/
theorem primitiveRoot_pairWeight_eq_pairWeight_candidates
    {F : Type*} [Field F] {n : ℕ} (hn : 2 ≤ n)
    (lambda : F) (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (a b c d : Fin n) (hcd : c ≠ d)
    (h : lambda ^ (2 ^ a.val + 2 ^ b.val) =
      lambda ^ (2 ^ c.val + 2 ^ d.val)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hfinite : IsOfFinOrder lambda :=
    hprim.isOfFinOrder (Nat.sub_ne_zero_of_lt
      (Nat.one_lt_pow (by omega : n ≠ 0) (by omega)))
  have hmod : Nat.ModEq (2 ^ n - 1)
      (2 ^ a.val + 2 ^ b.val) (2 ^ c.val + 2 ^ d.val) := by
    have h' := hfinite.pow_eq_pow_iff_modEq.mp h
    rwa [← hprim.eq_orderOf] at h'
  rcases lt_trichotomy c d with hlt | heq | hgt
  · let p : HigmanExponentPair n := ⟨(c, d), hlt⟩
    simpa only [p] using
      normalizedTwoPower_modEq_pairWeight_candidates hn a b p hmod
  · exact (hcd heq).elim
  · let p : HigmanExponentPair n := ⟨(d, c), hgt⟩
    rcases normalizedTwoPower_modEq_pairWeight_candidates
        hn a b p (by simpa only [p, add_comm] using hmod) with hp | hp
    · exact Or.inr hp
    · exact Or.inl hp

/-- In an odd cyclic index group, a nonzero gap `d` cannot have both of its
adjacent gaps `d-1` and `d+1` in the same unordered class `±r`. -/
theorem not_both_adjacent_pairGaps_of_odd
    {n : ℕ} (hnodd : Odd n) {d r : ZMod n} (hd : d ≠ 0) :
    ¬ ((d - 1 = r ∨ d - 1 = -r) ∧
      (d + 1 = r ∨ d + 1 = -r)) := by
  rintro ⟨hminus, hplus⟩
  have false_of_one_add_one_eq_zero
      (h : (1 : ZMod n) + 1 = 0) : False := by
    have hone : (1 : ZMod n) = 0 :=
      (ZMod.add_self_eq_zero_iff_eq_zero hnodd).mp h
    apply hd
    calc
      d = d * 1 := (mul_one d).symm
      _ = d * 0 := congrArg (d * ·) hone
      _ = 0 := mul_zero d
  rcases hminus with hminus | hminus <;>
    rcases hplus with hplus | hplus
  · apply false_of_one_add_one_eq_zero
    calc
      (1 : ZMod n) + 1 = (d + 1) - (d - 1) := by ring
      _ = r - r := by rw [hminus, hplus]
      _ = 0 := sub_self r
  · apply hd
    apply (ZMod.add_self_eq_zero_iff_eq_zero hnodd).mp
    calc
      d + d = (d - 1) + (d + 1) := by ring
      _ = r + -r := by rw [hminus, hplus]
      _ = 0 := add_neg_cancel r
  · apply hd
    apply (ZMod.add_self_eq_zero_iff_eq_zero hnodd).mp
    calc
      d + d = (d - 1) + (d + 1) := by ring
      _ = -r + r := by rw [hminus, hplus]
      _ = 0 := neg_add_cancel r
  · apply false_of_one_add_one_eq_zero
    calc
      (1 : ZMod n) + 1 = (d + 1) - (d - 1) := by ring
      _ = (-r) - (-r) := by rw [hminus, hplus]
      _ = 0 := sub_self (-r)

/-- **Higman Lemma 6 (p. 86), odd-gap obstruction in source indices.**

For `i < j`, the two repeated candidates use the inner pairs
`{i,j-1}` and `{j,i-1}` (indices modulo `n`). When `n` is odd, these
pairs cannot both have Higman's permitted gap `±r`. -/
theorem HigmanExponentPair.not_both_predecessor_pairGaps_of_odd
    {n : ℕ} [NeZero n] (hnodd : Odd n) (p : HigmanExponentPair n)
    (r : ZMod n) :
    ¬ (HasHigmanPairGap r p.1.1 (p.1.2 - 1) ∧
      HasHigmanPairGap r p.1.2 (p.1.1 - 1)) := by
  rintro ⟨hleft, hright⟩
  let d := higmanCyclicGap p.1.1 p.1.2
  have hd : d ≠ 0 := by
    intro hd0
    have heq : ZMod.finEquiv n p.1.2 = ZMod.finEquiv n p.1.1 :=
      sub_eq_zero.mp hd0
    exact (by omega : p.1.2 ≠ p.1.1) ((ZMod.finEquiv n).injective heq)
  have hgapMinus : higmanCyclicGap p.1.1 (p.1.2 - 1) = d - 1 := by
    simp only [higmanCyclicGap, d, map_sub, map_one]
    ring
  have hright' : HasHigmanPairGap r (p.1.1 - 1) p.1.2 :=
    HasHigmanPairGap.comm.mp hright
  have hgapPlus : higmanCyclicGap (p.1.1 - 1) p.1.2 = d + 1 := by
    simp only [higmanCyclicGap, d, map_sub, map_one]
    ring
  apply not_both_adjacent_pairGaps_of_odd hnodd hd
  constructor
  · simpa only [HasHigmanPairGap, hgapMinus] using hleft
  · simpa only [HasHigmanPairGap, hgapPlus] using hright'

/-! ## Pair-weight eigenspace spanning -/

universe uSpanK uSpanV uSpanW

/-- An equivariant alternating bilinear map with spanning range sends an eigenbasis to
pair-product eigenspaces spanning the codomain. Distinct unordered basis pairs are indexed
by their unique increasing ordered representatives. -/
theorem iSup_pairWeight_eigenspace_eq_top_of_bilinear
    {K : Type uSpanK} {V : Type uSpanV} {W : Type uSpanW}
    [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (n : ℕ) (T₁ : Module.End K V) (T₂ : Module.End K W)
    (b : Basis (Fin n) K V) (weight : Fin n → K)
    (hb : ∀ i, T₁ (b i) = weight i • b i)
    (β : LinearMap.BilinMap K V W)
    (hequiv : ∀ x y, T₂ (β x y) = β (T₁ x) (T₁ y))
    (halt : ∀ x, β x x = 0)
    (hspan : Submodule.span K
      (Set.range fun z : V × V => β z.1 z.2) = ⊤) :
    ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n =>
        weight p.1.1 * weight p.1.2), T₂.eigenspace mu = ⊤ := by
  let S : Submodule K W :=
    ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n =>
      weight p.1.1 * weight p.1.2), T₂.eigenspace mu
  have heigen (i j : Fin n) :
      T₂ (β (b i) (b j)) =
        (weight i * weight j) • β (b i) (b j) := by
    rw [hequiv, hb, hb]
    simp [smul_smul, mul_comm]
  have hbasisBracket (i j : Fin n) : β (b i) (b j) ∈ S := by
    rcases lt_trichotomy i j with hij | hij | hij
    · let p : HigmanExponentPair n := ⟨(i, j), hij⟩
      apply Submodule.mem_iSup_of_mem (weight i * weight j)
      apply Submodule.mem_iSup_of_mem (show
        weight i * weight j ∈ Set.range
          (fun p : HigmanExponentPair n => weight p.1.1 * weight p.1.2) from
        ⟨p, rfl⟩)
      exact Module.End.mem_eigenspace_iff.mpr (heigen i j)
    · subst j
      simpa only [halt] using S.zero_mem
    · let p : HigmanExponentPair n := ⟨(j, i), hij⟩
      apply Submodule.mem_iSup_of_mem (weight j * weight i)
      apply Submodule.mem_iSup_of_mem (show
        weight j * weight i ∈ Set.range
          (fun p : HigmanExponentPair n => weight p.1.1 * weight p.1.2) from
        ⟨p, rfl⟩)
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [mul_comm] using heigen i j
  have hmap2 : Submodule.map₂ β ⊤ ⊤ ≤ S := by
    rw [← b.span_eq, Submodule.map₂_span_span]
    apply Submodule.span_le.2
    rintro _ ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
    exact hbasisBracket i j
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact hmap2 (Submodule.apply_mem_map₂ β Submodule.mem_top Submodule.mem_top)

/-- Frobenius-power specialization in exactly the form consumed by
`higman_spectral_contradiction`. -/
theorem iSup_frobeniusPairWeight_eigenspace_eq_top_of_bilinear
    {K : Type uSpanK} {V : Type uSpanV} {W : Type uSpanW}
    [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (n : ℕ) (lambda : K)
    (T₁ : Module.End K V) (T₂ : Module.End K W)
    (b : Basis (Fin n) K V)
    (hb : ∀ i, T₁ (b i) = lambda ^ (2 ^ i.val) • b i)
    (β : LinearMap.BilinMap K V W)
    (hequiv : ∀ x y, T₂ (β x y) = β (T₁ x) (T₁ y))
    (halt : ∀ x, β x x = 0)
    (hspan : Submodule.span K
      (Set.range fun z : V × V => β z.1 z.2) = ⊤) :
    ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n =>
        lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)),
      T₂.eigenspace mu = ⊤ := by
  simpa only [pow_add] using
    iSup_pairWeight_eigenspace_eq_top_of_bilinear n T₁ T₂ b
      (fun i => lambda ^ (2 ^ i.val)) hb β hequiv halt hspan


/-- The spectral contradiction at the end of Higman's Lemma 4.

The substantial representation-theoretic input is isolated in `hspan`: after scalar extension,
the second layer is spanned by eigenspaces whose eigenvalues are pairwise products of distinct
Frobenius conjugates of `lambda`. -/
theorem higman_spectral_contradiction
    {F : Type uSpectrumF} {V : Type uSpectrumV}
    [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (n : ℕ) (_hn : 2 ≤ n) (lambda : F)
    (hprim : IsPrimitiveRoot lambda (2 ^ n - 1))
    (hspan : ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n ↦
        lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)), T.eigenspace mu = ⊤)
    (hlambda : T.HasEigenvalue lambda) : False := by
  let weight : HigmanExponentPair n → F := fun p ↦
    lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)
  have hmem : lambda ∈ Set.range weight := by
    by_contra hnot
    have hd := (Module.End.eigenspaces_iSupIndep T).disjoint_biSup hnot
    change ⨆ mu ∈ Set.range weight, T.eigenspace mu = ⊤ at hspan
    rw [hspan, disjoint_top] at hd
    exact hlambda hd
  obtain ⟨p, hp⟩ := hmem
  have hij : p.1.1.val < p.1.2.val := p.2
  have hjn : p.1.2.val < n := p.1.2.isLt
  have hpow_i_j : 2 ^ p.1.1.val < 2 ^ p.1.2.val :=
    Nat.pow_lt_pow_right (by omega) hij
  have hpow_j_n : 2 ^ (p.1.2.val + 1) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hpow_i_pos : 0 < 2 ^ p.1.1.val := by positivity
  have hpow_j_pos : 0 < 2 ^ p.1.2.val := by positivity
  have hsum_pos : 0 < 2 ^ p.1.1.val + 2 ^ p.1.2.val := by omega
  have hk_pos : 0 < 2 ^ p.1.1.val + 2 ^ p.1.2.val - 1 := by omega
  have hk_lt : 2 ^ p.1.1.val + 2 ^ p.1.2.val - 1 < 2 ^ n - 1 := by
    rw [pow_succ] at hpow_j_n
    omega
  have hlambda_ne : lambda ≠ 0 := by
    exact (hprim.isUnit (by omega)).ne_zero
  have hk_one : lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val - 1) = 1 := by
    apply (mul_right_cancel₀ hlambda_ne)
    rw [one_mul, ← pow_succ]
    rw [Nat.sub_add_cancel (by omega)]
    exact hp
  exact hprim.pow_ne_one_of_pos_of_lt (by omega) hk_lt hk_one



/-! ## Higman's Lemma 4 -/

universe uHelperF uHelperK uHelperC uHelperV uHelperW

/-- A C-equivariant linear equivalence transfers a base-changed eigenvector
equation from one representation to the other. -/
theorem baseChange_eigenvector_equation_of_equivariant_linearEquiv
    {F : Type uHelperF} {K : Type uHelperK} {C : Type uHelperC}
    {V : Type uHelperV} {W : Type uHelperW}
    [Field F] [Field K] [Algebra F K] [Group C]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (rhoV : Representation F C V) (rhoW : Representation F C W)
    (e : V ≃ₗ[F] W)
    (he : ∀ c v, e (rhoV c v) = rhoW c (e v))
    (c : C) (lambda : K) (x : K ⊗[F] V)
    (hx : (rhoV c).baseChange K x = lambda • x) :
    (rhoW c).baseChange K (e.baseChange F K V W x) =
      lambda • (e.baseChange F K V W x) := by
  have hinter : ∀ y : K ⊗[F] V,
      e.baseChange F K V W ((rhoV c).baseChange K y) =
        (rhoW c).baseChange K (e.baseChange F K V W y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp [he]
    | add y z hy hz => simp [hy, hz]
  rw [← hinter x, hx, map_smul]

universe uMain

/-- **Higman Lemma 4**. A faithful irreducible
cyclic action on V₁, a transitive action on the nonzero vectors of V₂, and a
full-span equivariant alternating bracket rule out an equivariant isomorphism. -/
theorem not_exists_equivariant_linearEquiv_of_higman_bracket
    {C V₁ V₂ : Type uMain}
    [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Finite V₂]
    (rho₁ : Representation (ZMod 2) C V₁)
    (rho₂ : Representation (ZMod 2) C V₂)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2) V₂ = n)
    (hirr₁ : Representation.IsIrreducible rho₁)
    (hfaith₁ : Function.Injective rho₁)
    (beta : LinearMap.BilinMap (ZMod 2) V₁ V₂)
    (hbetaEquiv : ∀ c x y,
      rho₂ c (beta x y) = beta (rho₁ c x) (rho₁ c y))
    (hbetaAlt : ∀ x, beta x x = 0)
    (hbetaSpan : Submodule.span (ZMod 2)
      (Set.range fun z : V₁ × V₁ => beta z.1 z.2) = ⊤)
    (htrans₂ : ∀ v w : V₂, v ≠ 0 → w ≠ 0 →
      ∃ c : C, rho₂ c v = w) :
    ¬ ∃ e : V₁ ≃ₗ[ZMod 2] V₂,
      ∀ c v, e (rho₁ c v) = rho₂ c (e v) := by
  rintro ⟨e, he⟩
  have hfin₁ : Module.finrank (ZMod 2) V₁ = n :=
    e.finrank_eq.trans hfin₂
  letI : Nontrivial V₂ :=
    Module.nontrivial_of_finrank_pos (by rw [hfin₂]; omega)
  have hfaith₂ : Function.Injective rho₂ :=
    representation_faithful_of_equivariant_linearEquiv
      rho₁ rho₂ e he hfaith₁
  obtain ⟨c, hc⟩ :=
    exists_generator_orderOf_eq_pow_sub_one_of_faithful_transitive_nonzero
      rho₂ n hfin₂ hfaith₂ htrans₂
  let K := GaloisField 2 n
  obtain ⟨_efield, lambda, b, hprim, _hconj, _hgen, hb⟩ :=
    exists_singerFrobeniusEigenbasis_of_faithful_irreducible
      rho₁ n hn hfin₁ hirr₁ hfaith₁ c hc
  let betaK : LinearMap.BilinMap K
      (K ⊗[ZMod 2] V₁) (K ⊗[ZMod 2] V₂) :=
    beta.baseChange K
  let T₁ : Module.End K (K ⊗[ZMod 2] V₁) := (rho₁ c).baseChange K
  let T₂ : Module.End K (K ⊗[ZMod 2] V₂) := (rho₂ c).baseChange K
  have hbetaEquivK : ∀ x y,
      T₂ (betaK x y) = betaK (T₁ x) (T₁ y) := by
    intro x y
    exact LinearMap.BilinMap.baseChange_equivariant
      beta (rho₁ c) (rho₂ c) (hbetaEquiv c) x y
  have hbetaAltK : ∀ x, betaK x x = 0 := by
    intro x
    exact LinearMap.BilinMap.zmodTwo_baseChange_self_eq_zero beta hbetaAlt x
  have hbetaSpanK : Submodule.span K
      (Set.range fun z : (K ⊗[ZMod 2] V₁) × (K ⊗[ZMod 2] V₁) =>
        betaK z.1 z.2) = ⊤ :=
    LinearMap.BilinMap.baseChange_span_eq_top beta hbetaSpan
  have hpairSpan : ⨆ mu ∈ Set.range (fun p : HigmanExponentPair n ↦
      lambda ^ (2 ^ p.1.1.val + 2 ^ p.1.2.val)),
      T₂.eigenspace mu = ⊤ :=
    iSup_frobeniusPairWeight_eigenspace_eq_top_of_bilinear
      n lambda T₁ T₂
      b hb betaK hbetaEquivK hbetaAltK hbetaSpanK
  let i₀ : Fin n := ⟨0, by omega⟩
  have hfirst : T₁ (b i₀) = lambda • b i₀ := by
    simpa [i₀] using hb i₀
  have hsecond : T₂
      (e.baseChange (ZMod 2) K V₁ V₂ (b i₀)) =
      lambda • (e.baseChange (ZMod 2) K V₁ V₂ (b i₀)) :=
    baseChange_eigenvector_equation_of_equivariant_linearEquiv
      rho₁ rho₂ e he c lambda (b i₀) hfirst
  have hsecondNe : e.baseChange (ZMod 2) K V₁ V₂ (b i₀) ≠ 0 :=
    (e.baseChange (ZMod 2) K V₁ V₂).map_ne_zero_iff.mpr (b.ne_zero i₀)
  have hlambda : T₂.HasEigenvalue lambda :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hsecond, hsecondNe⟩
  exact higman_spectral_contradiction T₂ n hn lambda hprim hpairSpan hlambda


/-! ## Higman's Lemma 4 corollary -/

/-- **Higman Lemma 4, Corollary** (p. 85). For every extension field `K/F₂`,
the base change of the second layer has no `C`-invariant `F₂`-subspace which
is `C`-isomorphic to the first layer. -/
theorem not_exists_injective_intertwiner_to_baseChange_of_higman_bracket
    {K : Type uK} {C V₁ V₂ : Type uMain}
    [Field K] [Algebra (ZMod 2) K]
    [CommGroup C] [IsCyclic C] [Finite C]
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [Finite V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] [Finite V₂]
    (rho₁ : Representation (ZMod 2) C V₁)
    (rho₂ : Representation (ZMod 2) C V₂)
    (n : ℕ) (hn : 2 ≤ n)
    (hfin₂ : Module.finrank (ZMod 2) V₂ = n)
    (hirr₁ : Representation.IsIrreducible rho₁)
    (hfaith₁ : Function.Injective rho₁)
    (beta : LinearMap.BilinMap (ZMod 2) V₁ V₂)
    (hbetaEquiv : ∀ c x y,
      rho₂ c (beta x y) = beta (rho₁ c x) (rho₁ c y))
    (hbetaAlt : ∀ x, beta x x = 0)
    (hbetaSpan : Submodule.span (ZMod 2)
      (Set.range fun z : V₁ × V₁ => beta z.1 z.2) = ⊤)
    (htrans₂ : ∀ v w : V₂, v ≠ 0 → w ≠ 0 →
      ∃ c : C, rho₂ c v = w) :
    ¬ ∃ f : V₁ →ₗ[ZMod 2] K ⊗[ZMod 2] V₂,
      Function.Injective f ∧
      ∀ c v, f (rho₁ c v) = (rho₂ c).baseChange K (f v) := by
  letI : Nontrivial V₂ :=
    Module.nontrivial_of_finrank_pos (by rw [hfin₂]; omega)
  have hirr₂ : Representation.IsIrreducible rho₂ :=
    representation_isIrreducible_of_transitive_nonzero rho₂ htrans₂
  rintro ⟨f, hf, hinter⟩
  obtain ⟨e, he⟩ :=
    OddOrder.RepresentationTheory.exists_equiv_of_injective_intertwiner_to_baseChange
      rho₁ rho₂ hirr₁ hirr₂ f hf hinter
  exact not_exists_equivariant_linearEquiv_of_higman_bracket
    rho₁ rho₂ n hn hfin₂ hirr₁ hfaith₁ beta hbetaEquiv hbetaAlt hbetaSpan htrans₂
    ⟨e, he⟩

end OddOrder.Higman.Suzuki2Groups
