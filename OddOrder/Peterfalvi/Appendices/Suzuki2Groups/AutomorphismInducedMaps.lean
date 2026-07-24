/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.End
import OddOrder.GroupTheory.CentralExtensionAutomorphisms
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.ModelCenters

/-!
# Induced maps of automorphisms of an anisotropic quadratic extension

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Proposition 2 (setup), p. 142.

Let `P = QuadraticExtension q basis` be the concrete central extension of
Lemma 1(b) and suppose the polarization of `q` has trivial radical.  Then
the embedded kernel `ι(W)` is exactly the center of `P`, so every
automorphism `α` of `P` restricts to `ι(W)` and descends to the quotient
coordinate: it induces additive maps `f_α : V → V` and `g_α : W → W` with
`g_α ∘ q = q ∘ f_α`.  The assignment `α ↦ f_α` is a homomorphism
`MulAut P →* Multiplicative (AddAut V)` (`AddAut` is additively written in
mathlib); when the values of `q` generate `W`, its kernel is the
inducing-the-identity subgroup of Lemma 1(d), hence an elementary abelian
`2`-group — the kernel statement of Proposition 2.

Main declarations:

* `QuadraticExtension.center_eq_range_inl` — `Z(P) = ι(W)`;
* `QuadraticExtension.autQuotientHom` — the homomorphism `α ↦ f_α` into
  `Multiplicative (AddAut V)`;
* `QuadraticExtension.map_inl` / `QuadraticExtension.autKernelFun_add` —
  the induced kernel map `g_α`;
* `QuadraticExtension.autKernel_squareMap` — `g_α (q v) = q (f_α v)`;
* `QuadraticExtension.ker_autQuotientHom` — the kernel of `α ↦ f_α` is the
  inducing-the-identity subgroup;
* `QuadraticExtension.isElementaryAbelian_ker_autQuotientHom` — hence
  elementary abelian of exponent `2`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open OddOrder.GroupTheory
open Module

namespace QuadraticExtension

noncomputable section

universe uV uW uI

variable {V : Type uV} {W : Type uW} {ι : Type uI}
  [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
  [LinearOrder ι]
  (q : QuadraticMap (ZMod 2) V W) (basis : Basis ι (ZMod 2) V)

private theorem add_self_zero (w : W) : w + w = 0 := by
  calc w + w = 2 • w := (two_nsmul w).symm
    _ = (2 : ZMod 2) • w := (Nat.cast_smul_eq_nsmul (ZMod 2) 2 w).symm
    _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

@[simp]
theorem extension_inl_quotient (w : Multiplicative W) :
    ((extension q basis).inl w).quotient = 0 :=
  rfl

@[simp]
theorem extension_inl_central (w : Multiplicative W) :
    ((extension q basis).inl w).central = w.toAdd :=
  rfl

section InducedMaps

variable (hrad : ∀ v : V, (∀ v' : V, q (v + v') = q v + q v') → v = 0)

/-- The quotient coordinate of the image of the standard lift `⟨v, 0⟩` — the
induced map `f_α` of Proposition 2, as a bare function. -/
def autQuotientFun (Φ : MulAut (QuadraticExtension q basis)) (v : V) : V :=
  (Φ ⟨v, 0⟩).quotient

/-- The kernel coordinate of the image of an embedded kernel element — the
induced map `g_α` of Proposition 2, as a bare function. -/
def autKernelFun (Φ : MulAut (QuadraticExtension q basis)) (w : W) : W :=
  (Φ ((extension q basis).inl (Multiplicative.ofAdd w))).central

include hrad

/-- Central elements have vanishing quotient coordinate when the
polarization of `q` has trivial radical. -/
theorem quotient_eq_zero_of_mem_center (z : QuadraticExtension q basis)
    (hz : z ∈ Subgroup.center (QuadraticExtension q basis)) :
    z.quotient = 0 := by
  have hcomm : ∀ v : V,
      q.toBilin basis v z.quotient = q.toBilin basis z.quotient v :=
    (BilinearTwistedProduct.mem_center_iff z).mp hz
  refine hrad _ fun v' => ?_
  have hexp : q (z.quotient + v') =
      q z.quotient + q v' +
        (q.toBilin basis z.quotient v' + q.toBilin basis v' z.quotient) := by
    rw [← toBilin_self q basis (z.quotient + v'),
      ← toBilin_self q basis z.quotient, ← toBilin_self q basis v']
    simp only [map_add, LinearMap.add_apply]
    abel
  rw [hexp, hcomm v', add_self_zero, add_zero]

/-- **The center of the model is the embedded kernel** (trivial radical). -/
theorem center_eq_range_inl :
    Subgroup.center (QuadraticExtension q basis) =
      (extension q basis).inl.range := by
  refine le_antisymm ?_ (range_inl_le_center q basis)
  intro z hz
  refine ⟨Multiplicative.ofAdd z.central, ?_⟩
  ext
  · exact (quotient_eq_zero_of_mem_center q basis hrad z hz).symm
  · rfl

/-- Automorphisms preserve the embedded kernel (it is the center, which is
characteristic). -/
theorem map_mem_range_inl_iff (Φ : MulAut (QuadraticExtension q basis))
    (x : QuadraticExtension q basis) :
    Φ x ∈ (extension q basis).inl.range ↔
      x ∈ (extension q basis).inl.range := by
  rw [← center_eq_range_inl q basis hrad]
  have h := Subgroup.characteristic_iff_comap_eq.mp
    (inferInstance :
      (Subgroup.center (QuadraticExtension q basis)).Characteristic) Φ
  constructor
  · intro hx
    have hmem : x ∈ (Subgroup.center
        (QuadraticExtension q basis)).comap Φ.toMonoidHom :=
      Subgroup.mem_comap.mpr hx
    rwa [h] at hmem
  · intro hx
    rw [← h] at hx
    exact Subgroup.mem_comap.mp hx

/-- The automorphism sends embedded kernel elements to embedded kernel
elements, by the coordinate given by `autKernelFun`. -/
theorem map_inl (Φ : MulAut (QuadraticExtension q basis)) (w : W) :
    Φ ((extension q basis).inl (Multiplicative.ofAdd w)) =
      (extension q basis).inl
        (Multiplicative.ofAdd (autKernelFun q basis Φ w)) := by
  obtain ⟨w', hw'⟩ := (map_mem_range_inl_iff q basis hrad Φ _).mpr
    ⟨Multiplicative.ofAdd w, rfl⟩
  rw [← hw']
  congr 1
  have hc : autKernelFun q basis Φ w =
      ((extension q basis).inl w').central := by
    rw [hw']
    rfl
  rw [extension_inl_central] at hc
  rw [hc, ofAdd_toAdd]

/-- The quotient coordinate of an image depends only on the quotient
coordinate: `(Φ x).quotient = f_Φ (x.quotient)`. -/
theorem map_quotient (Φ : MulAut (QuadraticExtension q basis))
    (x : QuadraticExtension q basis) :
    (Φ x).quotient = autQuotientFun q basis Φ x.quotient := by
  have hx : x = (⟨x.quotient, 0⟩ : QuadraticExtension q basis) *
      (extension q basis).inl (Multiplicative.ofAdd x.central) := by
    ext
    · simp
    · simp [BilinearTwistedProduct.mul_def]
  calc (Φ x).quotient
      = (Φ (⟨x.quotient, 0⟩ : QuadraticExtension q basis) *
          Φ ((extension q basis).inl
            (Multiplicative.ofAdd x.central))).quotient := by
        rw [← map_mul, ← hx]
    _ = autQuotientFun q basis Φ x.quotient := by
        rw [BilinearTwistedProduct.quotient_mul, map_inl q basis hrad,
          extension_inl_quotient, add_zero]
        rfl

/-- The induced quotient map is additive. -/
theorem autQuotientFun_add (Φ : MulAut (QuadraticExtension q basis))
    (v₁ v₂ : V) :
    autQuotientFun q basis Φ (v₁ + v₂) =
      autQuotientFun q basis Φ v₁ + autQuotientFun q basis Φ v₂ := by
  have hsplit : (⟨v₁ + v₂, 0⟩ : QuadraticExtension q basis) =
      (⟨v₁, 0⟩ : QuadraticExtension q basis) * ⟨v₂, 0⟩ *
        ((extension q basis).inl
          (Multiplicative.ofAdd (q.toBilin basis v₁ v₂)))⁻¹ := by
    ext
    · simp
    · simp [BilinearTwistedProduct.mul_def, BilinearTwistedProduct.inv_def]
  change (Φ ⟨v₁ + v₂, 0⟩).quotient = _
  rw [hsplit, map_mul, map_mul, map_inv, map_inl q basis hrad,
    BilinearTwistedProduct.quotient_mul, BilinearTwistedProduct.quotient_mul,
    BilinearTwistedProduct.quotient_inv, extension_inl_quotient, neg_zero,
    add_zero]
  rfl

/-- The induced kernel map is additive. -/
theorem autKernelFun_add (Φ : MulAut (QuadraticExtension q basis))
    (w₁ w₂ : W) :
    autKernelFun q basis Φ (w₁ + w₂) =
      autKernelFun q basis Φ w₁ + autKernelFun q basis Φ w₂ := by
  apply Multiplicative.ofAdd.injective
  apply (extension q basis).inl_injective
  rw [← map_inl q basis hrad, show Multiplicative.ofAdd (w₁ + w₂) =
      Multiplicative.ofAdd w₁ * Multiplicative.ofAdd w₂ from rfl,
    map_mul, map_mul, map_inl q basis hrad, map_inl q basis hrad, ← map_mul,
    ← ofAdd_add]

/-- **The compatibility of Proposition 2**: the induced maps intertwine the
square map, `g_Φ (q v) = q (f_Φ v)`. -/
theorem autKernel_squareMap (Φ : MulAut (QuadraticExtension q basis))
    (v : V) :
    autKernelFun q basis Φ (q v) = q (autQuotientFun q basis Φ v) := by
  have hsq := congrArg Φ (sq_eq_inl_q q basis ⟨v, 0⟩)
  rw [map_pow, map_inl q basis hrad,
    sq_eq_inl_q q basis (Φ ⟨v, 0⟩)] at hsq
  have hW := congrArg Multiplicative.toAdd
    ((extension q basis).inl_injective hsq.symm)
  simp only [toAdd_ofAdd] at hW
  exact hW

/-- The inverse automorphism undoes the induced quotient map. -/
theorem autQuotientFun_inv_comp (Φ : MulAut (QuadraticExtension q basis))
    (v : V) :
    autQuotientFun q basis Φ⁻¹ (autQuotientFun q basis Φ v) = v := by
  have h := map_quotient q basis hrad Φ⁻¹ (Φ ⟨v, 0⟩)
  rw [show Φ⁻¹ (Φ (⟨v, 0⟩ : QuadraticExtension q basis)) = ⟨v, 0⟩ from
    Φ.symm_apply_apply _] at h
  exact h.symm

/-- The induced quotient map `f_Φ`, as an additive automorphism of `V`. -/
def autQuotientAddEquiv (Φ : MulAut (QuadraticExtension q basis)) :
    V ≃+ V where
  toFun := autQuotientFun q basis Φ
  invFun := autQuotientFun q basis Φ⁻¹
  left_inv := autQuotientFun_inv_comp q basis hrad Φ
  right_inv := by
    intro v
    have h := autQuotientFun_inv_comp q basis hrad Φ⁻¹ v
    rwa [inv_inv] at h
  map_add' := autQuotientFun_add q basis hrad Φ

/-- **The homomorphism `α ↦ f_α` of Proposition 2**, from `MulAut P` to the
(multiplicatively rewritten) group of additive automorphisms of the
quotient coordinate space. -/
def autQuotientHom :
    MulAut (QuadraticExtension q basis) →* Multiplicative (AddAut V) :=
  MonoidHom.mk'
    (fun Φ => Multiplicative.ofAdd (autQuotientAddEquiv q basis hrad Φ)) (by
    intro Φ Ψ
    have hadd : autQuotientAddEquiv q basis hrad (Φ * Ψ) =
        autQuotientAddEquiv q basis hrad Φ +
          autQuotientAddEquiv q basis hrad Ψ := by
      ext v
      change autQuotientFun q basis (Φ * Ψ) v =
        autQuotientFun q basis Φ (autQuotientFun q basis Ψ v)
      exact map_quotient q basis hrad Φ (Ψ ⟨v, 0⟩)
    exact congrArg Multiplicative.ofAdd hadd)

@[simp]
theorem autQuotientHom_apply (Φ : MulAut (QuadraticExtension q basis))
    (v : V) :
    (autQuotientHom q basis hrad Φ).toAdd v = autQuotientFun q basis Φ v :=
  rfl

/-- The induced kernel map `g_Φ`, as an additive homomorphism. -/
def autKernelAddHom (Φ : MulAut (QuadraticExtension q basis)) : W →+ W :=
  AddMonoidHom.mk' (autKernelFun q basis Φ) (autKernelFun_add q basis hrad Φ)

section Kernel

variable (hspan : AddSubgroup.closure (Set.range fun v : V => q v) = ⊤)

include hspan

/-- If the induced quotient map is the identity and the values of `q`
generate `W`, the automorphism induces the identity on both end groups. -/
theorem inducesId_of_autQuotient_id
    (Φ : MulAut (QuadraticExtension q basis))
    (hq : ∀ v : V, autQuotientFun q basis Φ v = v) :
    (extension q basis).InducesId Φ := by
  have hker : ∀ w : W, autKernelFun q basis Φ w = w := by
    intro w
    have hwmem : w ∈ AddSubgroup.closure (Set.range fun v : V => q v) := by
      rw [hspan]
      exact AddSubgroup.mem_top w
    induction hwmem using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨v, rfl⟩ := hx
        rw [autKernel_squareMap q basis hrad, hq]
    | zero =>
        exact map_zero (autKernelAddHom q basis hrad Φ)
    | add x y hx hy ihx ihy =>
        rw [autKernelFun_add q basis hrad, ihx, ihy]
    | neg x hx ih =>
        rw [show autKernelFun q basis Φ (-x) =
          -(autKernelFun q basis Φ x) from
            map_neg (autKernelAddHom q basis hrad Φ) x, ih]
  constructor
  · intro w
    rw [← ofAdd_toAdd w, map_inl q basis hrad, hker]
  · intro e
    apply Multiplicative.toAdd.injective
    change (Φ e).quotient = e.quotient
    rw [map_quotient q basis hrad, hq]

/-- **The kernel of `α ↦ f_α`** is the inducing-the-identity subgroup of
Lemma 1(d). -/
theorem ker_autQuotientHom :
    (autQuotientHom q basis hrad).ker =
      (extension q basis).inducingIdAuts := by
  ext Φ
  rw [MonoidHom.mem_ker, GroupExtension.mem_inducingIdAuts_iff]
  constructor
  · intro h
    refine inducesId_of_autQuotient_id q basis hrad hspan Φ fun v => ?_
    have hv := congrArg (fun e : Multiplicative (AddAut V) => e.toAdd v) h
    simpa using hv
  · rintro ⟨hinl, hright⟩
    apply Multiplicative.toAdd.injective
    refine DFunLike.ext _ _ fun v => ?_
    change autQuotientFun q basis Φ v = v
    have h := hright (⟨v, 0⟩ : QuadraticExtension q basis)
    exact congrArg Multiplicative.toAdd h

/-- **The kernel statement of Proposition 2**: the kernel of `α ↦ f_α` is
an elementary abelian `2`-group. -/
theorem isElementaryAbelian_ker_autQuotientHom :
    IsElementaryAbelian 2 (autQuotientHom q basis hrad).ker := by
  rw [ker_autQuotientHom q basis hrad hspan]
  exact (extension q basis).isElementaryAbelian_inducingIdAuts
    (range_inl_le_center q basis)

end Kernel

end InducedMaps

end

end QuadraticExtension

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
