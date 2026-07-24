/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import OddOrder.GroupTheory.RepresentationTheory.SemilinearFieldAut
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AutomorphismInducedMaps
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.FieldModel
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ModelCenters

/-!
# Peterfalvi Appendix III, Proposition 2: automorphisms of `B(n, 1)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Proposition 2, pp. 142-143.

Let `P = B(n, 1, ε)` be the concrete central extension
`QuadraticExtension q basis` attached to the type-B square map
`q(a, b) = a² + εab + b²`, and let `E = F[α]` be the field model of
Proposition 1, so that `q` becomes the norm `x·x̄` of `E`.  Every
automorphism `Φ` of `P` induces the additive map `f_Φ` on the quotient
coordinate (`autQuotientFun`); transporting along `(a, b) ↦ a + bα`, the
induced map is a *semilinear* map of the field model:

* `exists_semilinear_of_aut` — `f_Φ(x) = λ·σ(x)` for some `λ ∈ E*` and
  `σ ∈ Aut(E)` (the forward half of Proposition 2).

The argument feeds the compatibility `g_Φ ∘ q = q ∘ f_Φ`
(`autKernel_squareMap`), rewritten through the norm identity of
Proposition 1 (`FieldModel.mul_conj`) and the automorphism expansion of
the kernel-side map (`exists_algAut_expansion_algebraMap_comp`), into the
coefficient-collapse theorem
(`exists_smul_algAut_of_norm_intertwiner`, the book's equations (3)/(4)).
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.RepresentationTheory
open FieldModel QuadraticExtension

noncomputable section

variable {F : Type*} [Field F] [CharP F 2] [Finite F] (ε : F)

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

local instance : Finite (FieldModel ε) :=
  Finite.of_equiv _ (equivProd ε).toEquiv

variable {ι : Type*} [LinearOrder ι]

/-- **Peterfalvi Appendix III, Proposition 2, forward half** (pp. 142-143):
under the field-model identification `(a, b) ↦ a + bα` of Proposition 1,
the additive map `f_Φ` induced on the quotient coordinate by any
automorphism `Φ` of the model `B(n, 1, ε)` is a semilinear map
`x ↦ λ·σ(x)` of the field model (`λ ≠ 0`, `σ ∈ Aut(E)`). -/
theorem exists_semilinear_of_aut
    (hq : (typeBQuadraticMap (1 : RingAut F) ε).Anisotropic)
    (basis : Module.Basis ι (ZMod 2) (F × F))
    (Φ : MulAut (QuadraticExtension
      (typeBQuadraticMap (1 : RingAut F) ε) basis)) :
    ∃ (lam : FieldModel ε) (σ : FieldModel ε ≃ₐ[ZMod 2] FieldModel ε),
      lam ≠ 0 ∧ ∀ v : F × F,
        equivProd ε (autQuotientFun
            (typeBQuadraticMap (1 : RingAut F) ε) basis Φ v) =
          lam * σ (equivProd ε v) := by
  classical
  haveI : Fact (Irreducible (fieldModelPoly ε)) :=
    ⟨fieldModelPoly_irreducible ε hq⟩
  letI : Fintype (FieldModel ε ≃ₐ[ZMod 2] FieldModel ε) := Fintype.ofFinite _
  have hε : ε ≠ 0 := epsilon_ne_zero_of_anisotropic ε hq
  have hrad : ∀ w : F × F,
      (∀ v' : F × F, typeBQuadraticMap (1 : RingAut F) ε (w + v') =
        typeBQuadraticMap (1 : RingAut F) ε w +
          typeBQuadraticMap (1 : RingAut F) ε v') → w = 0 :=
    fun w hadd => typeBQuadraticMap_radical_eq_zero 1 ε hε w hadd
  -- the conjugation as an `𝔽₂`-algebra automorphism
  set κ : FieldModel ε ≃ₐ[ZMod 2] FieldModel ε :=
    (conj ε).restrictScalars (ZMod 2) with hκdef
  have hκconj : ∀ x : FieldModel ε, κ x = conj ε x := fun _ => rfl
  have hκ1 : κ ≠ 1 := by
    intro h
    refine conj_ne_refl ε hε (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun h x
  have hκ2 : κ * κ = 1 := AlgEquiv.ext fun x => conj_conj ε x
  -- the transported induced map, as an `𝔽₂`-linear endomap of the model
  set fE : FieldModel ε →ₗ[ZMod 2] FieldModel ε :=
    AddMonoidHom.toZModLinearMap 2
      (((equivProd ε).toAddMonoidHom.comp
        (autQuotientAddEquiv _ basis hrad Φ).toAddMonoidHom).comp
        (equivProd ε).symm.toAddMonoidHom) with hfEdef
  have hfE : ∀ x : FieldModel ε,
      fE x = equivProd ε (autQuotientFun
        (typeBQuadraticMap (1 : RingAut F) ε) basis Φ
          ((equivProd ε).symm x)) := fun _ => rfl
  have hf : fE ≠ 0 := by
    intro h0
    have h1 : equivProd ε (autQuotientFun
        (typeBQuadraticMap (1 : RingAut F) ε) basis Φ
          ((equivProd ε).symm (equivProd ε
            ((autQuotientAddEquiv _ basis hrad Φ).symm (1, 0))))) = 0 := by
      rw [← hfE, h0, LinearMap.zero_apply]
    rw [LinearEquiv.symm_apply_apply] at h1
    have h2 : autQuotientFun (typeBQuadraticMap (1 : RingAut F) ε) basis Φ
        ((autQuotientAddEquiv _ basis hrad Φ).symm (1, 0)) =
          ((1 : F), (0 : F)) :=
      (autQuotientAddEquiv _ basis hrad Φ).apply_symm_apply (1, 0)
    rw [h2, LinearEquiv.map_eq_zero_iff] at h1
    exact one_ne_zero (congrArg Prod.fst h1)
  -- the kernel-side induced map, expanded over `Aut(E)`
  obtain ⟨μ, hμ⟩ := exists_algAut_expansion_algebraMap_comp
    (E := FieldModel ε) 2
    (AddMonoidHom.toZModLinearMap 2 (autKernelAddHom _ basis hrad Φ))
  -- the compatibility `g ∘ q = q ∘ f`, in norm-intertwiner form
  have hcompat : ∀ x : FieldModel ε,
      (∑ ρ : FieldModel ε ≃ₐ[ZMod 2] FieldModel ε,
        μ ρ * ρ (x * κ x)) = fE x * κ (fE x) := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := (equivProd ε).surjective x
    have hNx : x * κ x = algebraMap F (FieldModel ε)
        (typeBQuadraticMap (1 : RingAut F) ε (a, b)) := by
      rw [hκconj, ← hab]
      exact mul_conj ε a b
    have hfv : fE x = equivProd ε (autQuotientFun
        (typeBQuadraticMap (1 : RingAut F) ε) basis Φ (a, b)) := by
      rw [hfE, ← hab, LinearEquiv.symm_apply_apply]
    have hNfx : fE x * κ (fE x) = algebraMap F (FieldModel ε)
        (typeBQuadraticMap (1 : RingAut F) ε (autQuotientFun
          (typeBQuadraticMap (1 : RingAut F) ε) basis Φ (a, b))) := by
      rw [hκconj, hfv]
      have h := mul_conj ε
        (autQuotientFun (typeBQuadraticMap (1 : RingAut F) ε) basis Φ
          (a, b)).1
        (autQuotientFun (typeBQuadraticMap (1 : RingAut F) ε) basis Φ
          (a, b)).2
      rwa [Prod.mk.eta] at h
    calc (∑ ρ : FieldModel ε ≃ₐ[ZMod 2] FieldModel ε, μ ρ * ρ (x * κ x))
        = ∑ ρ : FieldModel ε ≃ₐ[ZMod 2] FieldModel ε,
            μ ρ * ρ (algebraMap F (FieldModel ε)
              (typeBQuadraticMap (1 : RingAut F) ε (a, b))) := by
          rw [hNx]
      _ = algebraMap F (FieldModel ε)
            (autKernelFun (typeBQuadraticMap (1 : RingAut F) ε) basis Φ
              (typeBQuadraticMap (1 : RingAut F) ε (a, b))) :=
          (hμ (typeBQuadraticMap (1 : RingAut F) ε (a, b))).symm
      _ = algebraMap F (FieldModel ε)
            (typeBQuadraticMap (1 : RingAut F) ε (autQuotientFun
              (typeBQuadraticMap (1 : RingAut F) ε) basis Φ (a, b))) := by
          rw [autKernel_squareMap _ basis hrad Φ (a, b)]
      _ = fE x * κ (fE x) := hNfx.symm
  obtain ⟨lam, σ, hlam, _, hfx⟩ :=
    exists_smul_algAut_of_norm_intertwiner (F := FieldModel ε)
      κ hκ1 hκ2 fE hf μ hcompat
  refine ⟨lam, σ, hlam, fun v => ?_⟩
  have h := hfx (equivProd ε v)
  rwa [hfE, LinearEquiv.symm_apply_apply] at h

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
