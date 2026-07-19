/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralGraded
import OddOrder.GroupTheory.RepresentationTheory.BaseChange
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.Algebra.Module.ZMod
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
open scoped TensorProduct IsMulCommutative

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
universe uGenerator

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
    {F : Type uHelperF} {C : Type uHelperC} {V : Type uHelperV} {W : Type uHelperW}
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
