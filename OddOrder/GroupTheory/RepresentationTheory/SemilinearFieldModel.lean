/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppC_NormSet

/-!
# Generic semilinear `(9.7.b)` field-model realization `F_{r^s} ⋊ V*`  (issue 9078)

A **module-level generic** interface realizing the BG Appendix C Frobenius group
`normOneFrobeniusGroup r s = additiveFieldGroup r s ⋊ normOneUnits r s` (`= F_{r^s} ⋊ V*`) as a
subgroup of an ambient finite group `G`, from two pieces of data:

* an **additive field iso** `e : Additive ↥E ≃+ 𝔽_{r^s}` identifying an elementary-abelian kernel
  subgroup `E ≤ G` with the additive group of `𝔽_{r^s}` (the (9.7.b) field model, produced from
  App.B `exists_field_semilinear` on the caller's side);
* a **multiplicative character** `μ : ↥C →* 𝔽_{r^s}ˣ` realizing a complement `C ≤ G` as the
  norm-one units `V*` (`μ` injective with `μ.range = normOneUnits r s`, the Singer datum on the
  caller's side).

Given a compatibility (the `C`-conjugation on `E` matches `μ`-scalar multiplication) and the
disjointness `E ⊓ C = ⊥`, `fieldModelEmbedding` assembles the injective `σ : F_{r^s} ⋊ V* →* G`
(a `SemidirectProduct.lift`) whose additive kernel maps onto `E` and whose complement maps onto `C`.

This is the **side-agnostic** core shared by the `S`-side field-normalizer embedding
(`fieldNormalizerData_of_repr`, `P`/`U`) and the `T`-side model (`TFieldModelData`, `Q`/`V`); each
side instantiates it with its own `(E, C, e, μ)`.  Cf. Peterfalvi `(14.2)(a)`/`(14.4)`, BG App. C.

## References

* BG, *Local Analysis for the Odd Order Theorem*, Appendix C (`normOneFrobeniusGroup`).
* Peterfalvi, *Character Theory for the Odd Order Theorem*, §9 (9.7.b), §14 (14.2)(a)/(14.4).
* `issues/9078-semilinear-fieldmodel-leaf.md`, `9077` (HUB RULING B), `9000` scope note item 2.
-/

namespace OddOrder.RepresentationTheory.SemilinearFieldModel

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

/-! ## The kernel transport `F_{r^s} → G`

The additive `(inl)` factor of the embedding: transport `m ∈ additiveFieldGroup r s` through the
field iso `e` into the elementary-abelian subgroup `E ≤ G`.  Injective with image exactly `E`.
Generic version of `fieldNormalizerKernelTransport` (`S16_NonExistenceG`, `E = P`). -/

/-- **Kernel transport** `additiveFieldGroup r s →* G` for a field iso `e : Additive ↥E ≃+ 𝔽_{r^s}`.
Coordinate-wise `m ↦ ↑(toMul (e.symm (toAdd m)))`. -/
noncomputable def kernelTransport {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) :
    additiveFieldGroup r s →* G where
  toFun := fun m => ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥E) : G)
  map_one' := by simp
  map_mul' := fun m n => by simp [toAdd_mul, map_add, toMul_add]

@[simp] theorem kernelTransport_apply {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) (m : additiveFieldGroup r s) :
    kernelTransport e m = ((Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥E) : G) :=
  rfl

theorem kernelTransport_injective {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) :
    Function.Injective (kernelTransport e) := by
  intro m n hmn
  rw [kernelTransport_apply, kernelTransport_apply] at hmn
  have h1 : (Additive.toMul (e.symm (Multiplicative.toAdd m)) : ↥E) =
      Additive.toMul (e.symm (Multiplicative.toAdd n)) := Subtype.ext hmn
  have h2 : e.symm (Multiplicative.toAdd m) = e.symm (Multiplicative.toAdd n) :=
    Additive.toMul.injective h1
  exact Multiplicative.toAdd.injective (e.symm.injective h2)

theorem kernelTransport_range {r s : ℕ} [Fact r.Prime] {E : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s) :
    (kernelTransport e).range = E := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [kernelTransport_apply]
    exact (Additive.toMul (e.symm (Multiplicative.toAdd m))).2
  · intro g hg
    refine ⟨Multiplicative.ofAdd (e (Additive.ofMul (⟨g, hg⟩ : ↥E))), ?_⟩
    rw [kernelTransport_apply]
    simp

end OddOrder.RepresentationTheory.SemilinearFieldModel
