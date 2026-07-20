/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Scalar extension (base change) of group representations

Shared `OddOrder.GroupTheory.RepresentationTheory` module: extend a representation
`ρ : Representation F G V` along a field extension `K / F` to
`Representation K G (K ⊗[F] V)`.

This is the bridge used by Bender–Glauberman §2/§3 (and BG Thm 2.6(b)) to reduce a
representation over an arbitrary field `F` (with `char F ∤ |G|`) to one over the algebraic
closure `F* = AlgebraicClosure F`, where the representation theory of (extra)special groups is
available.  BG Thm 2.5's proof opens with exactly this step ("Let `F*` be the algebraic closure
of `F` and `V* = F* ⊗_F V`").

## Main definitions / results

* `baseChangeRepresentation K ρ` — the scalar extension `Representation K G (K ⊗[F] V)`.
* `baseChangeRepresentation_apply_tmul` — action on a simple tensor.
* `baseChangeRepresentation_faithful` — faithfulness survives a faithfully flat extension.
* `LinearMap.baseChange₂ A b` — scalar extension of a mixed bilinear map
  `M →ₗ[R] N →ₗ[R] P` in both inputs and its output.

The fixed-space / `C_V(R)` transfer lemmas (`C_V(R) = 0 ⟹ C_{V*}(R) = 0`, dimension invariance)
build on this; see the `invariants` lemmas below.
-/

open scoped TensorProduct

namespace LinearMap

universe uMixedR uMixedA uMixedM uMixedN uMixedP

variable {R : Type uMixedR} {A : Type uMixedA}
variable {M : Type uMixedM} {N : Type uMixedN} {P : Type uMixedP}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

variable (A) in
/-- Extend scalars in both inputs and the output of a mixed bilinear map.

Unlike `LinearMap.BilinMap.baseChange`, the two input modules may differ. -/
def baseChange₂ (b : M →ₗ[R] N →ₗ[R] P) :
    (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) →ₗ[A] (A ⊗[R] P) :=
  (TensorProduct.lift.equiv (.id A)
      (A ⊗[R] M) (A ⊗[R] N) (A ⊗[R] P)).symm
    ((TensorProduct.lift b).baseChange A ∘ₗ
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A M N).symm.toLinearMap)

/-- Evaluation of `baseChange₂` on pure tensors. -/
@[simp]
theorem baseChange₂_tmul (b : M →ₗ[R] N →ₗ[R] P)
    (a c : A) (m : M) (n : N) :
    b.baseChange₂ A (a ⊗ₜ[R] m) (c ⊗ₜ[R] n) =
      (a * c) ⊗ₜ[R] b m n := by
  simp [baseChange₂]

/-- Equivariance of a mixed bilinear map survives extension of scalars. -/
theorem baseChange₂_equivariant
    (b : M →ₗ[R] N →ₗ[R] P)
    (Tₘ : Module.End R M) (Tₙ : Module.End R N) (Tₚ : Module.End R P)
    (h : ∀ x y, Tₚ (b x y) = b (Tₘ x) (Tₙ y))
    (u : A ⊗[R] M) (v : A ⊗[R] N) :
    Tₚ.baseChange A (b.baseChange₂ A u v) =
      b.baseChange₂ A (Tₘ.baseChange A u) (Tₙ.baseChange A v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul c y => simp [h]
      | add v w hv hw => simp [hv, hw]
  | add u w hu hw => simp [hu, hw]

/-- Full spanning range of a mixed bilinear map survives scalar extension. -/
theorem baseChange₂_span_eq_top
    (b : M →ₗ[R] N →ₗ[R] P)
    (hspan : Submodule.span R
      (Set.range fun z : M × N => b z.1 z.2) = ⊤) :
    Submodule.span A
      (Set.range fun z : (A ⊗[R] M) × (A ⊗[R] N) =>
        b.baseChange₂ A z.1 z.2) = ⊤ := by
  let f : (M ⊗[R] N) →ₗ[R] P := TensorProduct.lift b
  have hsets :
      Set.image2 (fun x y => b x y)
          (↑(⊤ : Submodule R M) : Set M)
          (↑(⊤ : Submodule R N) : Set N) =
        Set.range (fun z : M × N => b z.1 z.2) := by
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
          (TensorProduct.mapIncl (⊤ : Submodule R M) (⊤ : Submodule R N)) = ⊤ := by
    rw [TensorProduct.range_mapIncl, TensorProduct.map₂_mk_top_top_eq_top]
  have hrange : LinearMap.range f = ⊤ := by
    rw [← LinearMap.range_comp_of_range_eq_top f hmapIncl]
    rw [← TensorProduct.map₂_eq_range_lift_comp_mapIncl, hmap2]
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp hrange
  have hsurjA : Function.Surjective (f.baseChange A) :=
    LinearMap.baseChange_surjective A hsurj
  let S : Submodule A (A ⊗[R] P) :=
    Submodule.span A
      (Set.range fun z : (A ⊗[R] M) × (A ⊗[R] N) =>
        b.baseChange₂ A z.1 z.2)
  have hsimple (a : A) (t : M ⊗[R] N) :
      f.baseChange A (a ⊗ₜ[R] t) ∈ S := by
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
  obtain ⟨t, rfl⟩ := hsurjA z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => exact hsimple a t
  | add t w ht hw =>
      rw [map_add]
      exact S.add_mem ht hw

end LinearMap

namespace OddOrder.RepresentationTheory

/-! ## Frobenius on the scalar factor -/

universe uFrobeniusL uFrobeniusV uFrobeniusW

/-- Absolute Frobenius on the scalar factor of an `F₂` base change. -/
noncomputable def frobeniusScalarBaseChange
    (L : Type uFrobeniusL) [Field L] [Finite L] [Algebra (ZMod 2) L]
    {V : Type uFrobeniusV} [AddCommMonoid V] [Module (ZMod 2) V] :
    (L ⊗[ZMod 2] V) →ₗ[ZMod 2] (L ⊗[ZMod 2] V) := by
  letI : Fintype L := Fintype.ofFinite L
  exact TensorProduct.map
    (FiniteField.frobeniusAlgHom (ZMod 2) L).toLinearMap
    (LinearMap.id : V →ₗ[ZMod 2] V)

@[simp]
theorem frobeniusScalarBaseChange_tmul
    (L : Type uFrobeniusL) [Field L] [Finite L] [Algebra (ZMod 2) L]
    {V : Type uFrobeniusV} [AddCommMonoid V] [Module (ZMod 2) V]
    (a : L) (v : V) :
    frobeniusScalarBaseChange L (a ⊗ₜ[ZMod 2] v) =
      (a ^ 2) ⊗ₜ[ZMod 2] v := by
  simp [frobeniusScalarBaseChange]

/-- Frobenius on the scalar factor commutes with extension of a ground-field
bilinear map. -/
theorem frobeniusScalarBaseChange_bilin
    (L : Type uFrobeniusL) [Field L] [Finite L] [Algebra (ZMod 2) L]
    {V : Type uFrobeniusV} {W : Type uFrobeniusW}
    [AddCommMonoid V] [Module (ZMod 2) V]
    [AddCommMonoid W] [Module (ZMod 2) W]
    (B : LinearMap.BilinMap (ZMod 2) V W)
    (x y : L ⊗[ZMod 2] V) :
    frobeniusScalarBaseChange L (B.baseChange L x y) =
      B.baseChange L
        (frobeniusScalarBaseChange L x)
        (frobeniusScalarBaseChange L y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b v => simp [mul_pow]
      | add y z hy hz => simp [hy, hz]
  | add x z hx hz => simp [hx, hz]

/-- Scalar extension of a representation along a field extension.

The concrete base-change object `Representation K G (K ⊗[F] V)`: `g` acts by `id_K ⊗ ρ g`. -/
noncomputable def baseChangeRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) :
    Representation K G (TensorProduct F K V) where
  toFun g := TensorProduct.AlgebraTensorModule.map (R := F) (A := K)
    (M := K) (N := V) (P := K) (Q := V)
    (LinearMap.id : K →ₗ[K] K) (ρ g)
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp [map_mul]

/-- `baseChangeRepresentation` の単純テンソル上の作用: `a ⊗ₜ v ↦ a ⊗ₜ ρ g v`. -/
@[simp]
theorem baseChangeRepresentation_apply_tmul
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (g : G) (a : K) (v : V) :
    baseChangeRepresentation K ρ g (a ⊗ₜ[F] v) = a ⊗ₜ[F] ρ g v := by
  simp [baseChangeRepresentation]

/-- Faithfulness survives scalar extension along a faithfully flat field extension.

For the algebraic-closure route, `K` will be `AlgebraicClosure F`.  The proof uses the canonical
injection `V → K ⊗[F] V`. -/
theorem baseChangeRepresentation_faithful
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K] [Module.FaithfullyFlat F K]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) :
    Function.Injective (baseChangeRepresentation K ρ) := by
  intro g h hgh
  apply hfaithful
  ext v
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := K) V
  have hmap := congrArg
    (fun f : TensorProduct F K V →ₗ[K] TensorProduct F K V => f (1 ⊗ₜ[F] v)) hgh
  simpa [baseChangeRepresentation] using hmap

/-- The obstruction map `v ↦ (g ↦ ρ g v - v)`; its kernel is the space of invariants. -/
private noncomputable def invariantsObstruction
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    V →ₗ[F] (G → V) :=
  LinearMap.pi (fun g => ρ g - LinearMap.id)

private theorem ker_invariantsObstruction
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V) :
    LinearMap.ker (invariantsObstruction ρ) = Representation.invariants ρ := by
  ext v
  rw [LinearMap.mem_ker, Representation.mem_invariants, funext_iff]
  refine forall_congr' (fun g => ?_)
  simp [invariantsObstruction, LinearMap.pi_apply, LinearMap.sub_apply, sub_eq_zero]

/-- **Base change preserves vanishing of invariants**: if a representation `ρ` over a field `F`
has no nonzero invariants, then neither does its scalar extension to any field extension `K/F`.

This is the field-agnostic bridge that transfers a hypothesis `C_V(R) = 0` to the algebraic
closure (BG §2/§3): apply it to the restricted representation `ρ.comp R.subtype`.  The proof
factors the invariants as `ker` of the obstruction map `v ↦ (g ↦ ρ g v - v)`; flatness of `K`
over `F` preserves the injectivity of that map, and `TensorProduct.piRight` identifies its scalar
extension with the obstruction map of the base-changed representation. -/
theorem invariants_baseChangeRepresentation_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (h : Representation.invariants ρ = ⊥) :
    Representation.invariants (baseChangeRepresentation K ρ) = ⊥ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set ρ' := baseChangeRepresentation K ρ with hρ'
  -- `ρ`'s obstruction map is injective (its kernel is the invariants, which vanish).
  have hinj : Function.Injective (invariantsObstruction ρ) := by
    rw [← LinearMap.ker_eq_bot, ker_invariantsObstruction, h]
  -- flatness of `K/F` preserves injectivity under `lTensor`.
  have hlt : Function.Injective (LinearMap.lTensor K (invariantsObstruction ρ)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  -- `piRight ∘ lTensor` agrees with `ρ'`'s obstruction map on the nose.
  have hcompat : ∀ x : TensorProduct F K V,
      invariantsObstruction ρ' x
        = TensorProduct.piRight F K K (fun _ : G => V)
            (LinearMap.lTensor K (invariantsObstruction ρ) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        funext g
        simp [invariantsObstruction, hρ', LinearMap.pi_apply, LinearMap.sub_apply,
          baseChangeRepresentation_apply_tmul, LinearMap.lTensor_tmul,
          TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => simp [map_add, hx, hy]
  -- hence `ρ'`'s obstruction map is injective, so its invariants vanish.
  have hinj' : Function.Injective (invariantsObstruction ρ') := by
    have hfun : (invariantsObstruction ρ' : TensorProduct F K V → (G → TensorProduct F K V))
        = (TensorProduct.piRight F K K (fun _ : G => V)) ∘
            (LinearMap.lTensor K (invariantsObstruction ρ)) := funext hcompat
    rw [show ⇑(invariantsObstruction ρ') = _ from hfun]
    exact (TensorProduct.piRight F K K (fun _ : G => V)).injective.comp hlt
  rw [← ker_invariantsObstruction ρ', LinearMap.ker_eq_bot.mpr hinj']

/-- **Base change preserves the dimension of the invariants** (BG (2.9), dimension form).  For a
finite group `G` and a field extension `K/F`, the `K`-dimension of `C_{K⊗V}(G)` equals the
`F`-dimension of `C_V(G)`.

The space of invariants is the kernel of the obstruction map `f : v ↦ (g ↦ ρ g v - v)`; the
obstruction map of the base-changed representation factors as `piRight ∘ (K ⊗ f)`, so its kernel
(over `K`) equals `ker (K ⊗ f)`.  Flatness of `K/F` (`Module.Flat.ker_lTensor_eq`) identifies that
kernel with `K ⊗ ker f`, whose `K`-dimension is `finrank F (ker f) = finrank F C_V(G)`
(`Module.finrank_baseChange`).

Applied to `ρ.comp R.subtype` this transfers `dim C_V(R) = 1` to the algebraic closure, the
hypothesis form needed by BG Theorem 3.5. -/
theorem finrank_invariants_baseChangeRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) :
    Module.finrank K (Representation.invariants (baseChangeRepresentation K ρ))
      = Module.finrank F (Representation.invariants ρ) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set f := invariantsObstruction ρ with hf
  set e := TensorProduct.piRight F K K (fun _ : G => V) with he
  -- the `K`-linear obstruction map of `baseChange ρ` factors as `e ∘ (K ⊗ f)`.
  have hfactor : invariantsObstruction (baseChangeRepresentation K ρ)
      = e.toLinearMap ∘ₗ TensorProduct.AlgebraTensorModule.lTensor K K f := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        funext g
        simp only [hf, he, invariantsObstruction, LinearMap.pi_apply, LinearMap.sub_apply,
          LinearMap.id_coe, id_eq, baseChangeRepresentation_apply_tmul, LinearMap.comp_apply,
          TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearEquiv.coe_coe,
          TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  -- kernels agree (`e` is an isomorphism).
  have hkere : LinearMap.ker e.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hker : LinearMap.ker (invariantsObstruction (baseChangeRepresentation K ρ))
      = LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor K K f) := by
    rw [hfactor, LinearMap.ker_comp, hkere, Submodule.comap_bot]
  -- `K ⊗ (subtype of ker f)` is injective (flatness), so its range has dimension
  -- `finrank F (ker f)`.
  have hinj : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor K K
      (LinearMap.ker f).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (LinearMap.ker f).subtype (Submodule.injective_subtype _)
  rw [← ker_invariantsObstruction (baseChangeRepresentation K ρ), hker,
    Module.Flat.ker_lTensor_eq K K f, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_baseChange, hf, ker_invariantsObstruction]

/-- Base change commutes with restriction along a group hom `φ : H →* G`.

Lets the whole-group transfer lemmas apply to a subgroup: with `φ = H.subtype` and `ρ.comp φ`
the restricted representation, `C_V(H) = ⊥` over `F` transfers to `C_{K⊗V}(H) = ⊥` over `K`
(this is the form of BG (2.9), used at `H = Z(P)`). -/
@[simp]
theorem baseChangeRepresentation_comp
    {F : Type*} [Field F] {G H : Type*} [Group G] [Group H]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Type*) [Field K] [Algebra F K]
    (ρ : Representation F G V) (φ : H →* G) :
    baseChangeRepresentation K (ρ.comp φ) = (baseChangeRepresentation K ρ).comp φ := rfl


/-! ## Detecting invariant copies after base change -/

universe uBaseChangeF uBaseChangeK uBaseChangeC uBaseChangeV uBaseChangeW

/-- The coefficient of a base-changed vector at one basis element of the
extension field. This is kept private; the public API is the descent theorem
below. -/
private noncomputable def baseChangeCoordinate
    {F : Type uBaseChangeF} {K : Type uBaseChangeK}
    {V : Type uBaseChangeV} {ι : Type*}
    [Field F] [AddCommGroup K] [Module F K]
    [AddCommGroup V] [Module F V] [DecidableEq ι]
    (b : Module.Basis ι F K) (i : ι) : K ⊗[F] V →ₗ[F] V where
  toFun z := TensorProduct.equivFinsuppOfBasisLeft b z i
  map_add' x y := by simp
  map_smul' a x := by simp

/-- Taking one coefficient in the extension-field factor commutes with every
endomorphism defined over the ground field. -/
private theorem baseChangeCoordinate_apply_baseChange
    {F : Type uBaseChangeF} {K : Type uBaseChangeK}
    {V : Type uBaseChangeV} {ι : Type*}
    [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module F V] [DecidableEq ι]
    (b : Module.Basis ι F K) (i : ι) (T : Module.End F V)
    (z : K ⊗[F] V) :
    baseChangeCoordinate (F := F) (K := K) (V := V) b i (T.baseChange K z) =
      T (baseChangeCoordinate (F := F) (K := K) (V := V) b i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [baseChangeCoordinate]
  | tmul a v => simp [baseChangeCoordinate]
  | add x y hx hy => simp [hx, hy]

/-- An injective ground-field-linear intertwiner from an irreducible
representation into the base change of another irreducible representation
descends to an equivalence of the original representations. -/
theorem exists_equiv_of_injective_intertwiner_to_baseChange
    {F : Type uBaseChangeF} {K : Type uBaseChangeK}
    {C : Type uBaseChangeC} {V : Type uBaseChangeV}
    {W : Type uBaseChangeW}
    [Field F] [Field K] [Algebra F K] [Group C]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (rhoV : Representation F C V) (rhoW : Representation F C W)
    (hirrV : Representation.IsIrreducible rhoV)
    (hirrW : Representation.IsIrreducible rhoW)
    (f : V →ₗ[F] K ⊗[F] W)
    (hf : Function.Injective f)
    (hinter : ∀ c v, f (rhoV c v) = (rhoW c).baseChange K (f v)) :
    ∃ e : V ≃ₗ[F] W, ∀ c v, e (rhoV c v) = rhoW c (e v) := by
  letI : Representation.IsIrreducible rhoV := hirrV
  letI : Representation.IsIrreducible rhoW := hirrW
  haveI : Nontrivial V := by
    haveI : Nontrivial (Subrepresentation rhoV) := IsSimpleOrder.toNontrivial
    have hsub : Nontrivial (Submodule F V) :=
      (Subrepresentation.toSubmodule_injective (ρ := rhoV)).nontrivial
    exact (Submodule.nontrivial_iff F).mp hsub
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hfv : f v ≠ 0 := by
    intro hzero
    apply hv
    apply hf
    simpa using hzero
  classical
  let bK := Module.Free.chooseBasis F K
  let eK := TensorProduct.equivFinsuppOfBasisLeft (N := W) bK
  have heK : eK (f v) ≠ 0 := by
    intro hzero
    apply hfv
    apply eK.injective
    simpa using hzero
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp heK
  have hi' : eK (f v) i ≠ 0 := by simpa using hi
  let g : V →ₗ[F] W := (baseChangeCoordinate bK i).comp f
  have hgv : g v ≠ 0 := by
    change eK (f v) i ≠ 0
    exact hi'
  have hginter : ∀ c x, g (rhoV c x) = rhoW c (g x) := by
    intro c x
    change baseChangeCoordinate bK i (f (rhoV c x)) =
      rhoW c (baseChangeCoordinate bK i (f x))
    rw [hinter]
    exact baseChangeCoordinate_apply_baseChange bK i (rhoW c) (f x)
  let gi : Representation.IntertwiningMap rhoV rhoW :=
    g.intertwiningMap_of_isIntertwiningMap rhoV rhoW hginter
  have hgi : gi ≠ 0 := by
    intro hzero
    have hz : gi v = 0 := by rw [hzero]; rfl
    exact hgv hz
  have hbij : Function.Bijective gi :=
    (Representation.IsIrreducible.bijective_or_eq_zero gi).resolve_right hgi
  let e := gi.ofBijective hbij
  refine ⟨e.toLinearEquiv, ?_⟩
  intro c x
  change g (rhoV c x) = rhoW c (g x)
  exact hginter c x

end OddOrder.RepresentationTheory
