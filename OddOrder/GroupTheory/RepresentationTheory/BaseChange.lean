/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
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

The fixed-space / `C_V(R)` transfer lemmas (`C_V(R) = 0 ⟹ C_{V*}(R) = 0`, dimension invariance)
build on this; see the `invariants` lemmas below.
-/

namespace OddOrder.RepresentationTheory

open scoped TensorProduct

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

end OddOrder.RepresentationTheory
