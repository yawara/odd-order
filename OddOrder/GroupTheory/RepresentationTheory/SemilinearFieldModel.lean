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

/-! ## The complement transport `V* → G`

The multiplicative `(inr)` factor: transport a norm-one unit `u* ∈ normOneUnits r s` through the
inverse of `μ` into the complement `C ≤ G`.  Injective with image exactly `C`.  Generic version of
`fieldNormalizerComplementTransport` (`S16_NonExistenceG`, `C = U`). -/

/-- The `C ≃* normOneUnits r s` equivalence packaged from an injective `μ : ↥C →* 𝔽_{r^s}ˣ` with
`μ.range = normOneUnits r s`.  Its inverse, post-composed with `C ↪ G`, is `complementTransport`. -/
noncomputable def complementEquiv {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    ↥C ≃* ↥(normOneUnits r s) :=
  MulEquiv.ofBijective
    ({ toFun := fun c => ⟨μ c, hμ_range ▸ MonoidHom.mem_range.mpr ⟨c, rfl⟩⟩
       map_one' := by ext; simp
       map_mul' := fun a b => by ext; simp } : ↥C →* ↥(normOneUnits r s))
    ⟨fun a b h => hμ_inj (congrArg Subtype.val h),
     fun u => by
       obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (by rw [hμ_range]; exact u.2)
       exact ⟨v, Subtype.ext hv⟩⟩

/-- **Complement transport** `normOneUnits r s →* G` inverting `μ` and including back into `G`. -/
noncomputable def complementTransport {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    ↥(normOneUnits r s) →* G :=
  C.subtype.comp (complementEquiv μ hμ_inj hμ_range).symm.toMonoidHom

/-- Defining property: each `u* ∈ normOneUnits r s` has a preimage `v ∈ C` with `μ v = u*` and
`complementTransport … u* = ↑v`. -/
theorem complementTransport_exists {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) (u : ↥(normOneUnits r s)) :
    ∃ v : ↥C, (μ v : (GaloisField r s)ˣ) = (u : (GaloisField r s)ˣ) ∧
        complementTransport μ hμ_inj hμ_range u = (v : G) := by
  refine ⟨(complementEquiv μ hμ_inj hμ_range).symm u, ?_, rfl⟩
  have hval : ((complementEquiv μ hμ_inj hμ_range) ((complementEquiv μ hμ_inj hμ_range).symm u) :
      ↥(normOneUnits r s)) = u := (complementEquiv μ hμ_inj hμ_range).apply_symm_apply u
  exact congrArg Subtype.val hval

theorem complementTransport_injective {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    Function.Injective (complementTransport μ hμ_inj hμ_range) := by
  intro a b hab
  obtain ⟨va, hva_mu, hva⟩ := complementTransport_exists μ hμ_inj hμ_range a
  obtain ⟨vb, hvb_mu, hvb⟩ := complementTransport_exists μ hμ_inj hμ_range b
  rw [hva, hvb] at hab
  have hvab : va = vb := Subtype.ext hab
  exact Subtype.ext (by rw [← hva_mu, ← hvb_mu, hvab])

theorem complementTransport_range {r s : ℕ} [Fact r.Prime] {C : Subgroup G}
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s) :
    (complementTransport μ hμ_inj hμ_range).range = C := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨v, _, hv⟩ := complementTransport_exists μ hμ_inj hμ_range u
    rw [hv]; exact v.2
  · intro g hg
    refine ⟨(complementEquiv μ hμ_inj hμ_range) ⟨g, hg⟩, ?_⟩
    simp only [complementTransport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, Subgroup.coe_subtype]

/-! ## The field-model embedding `σ : F_{r^s} ⋊ V* → G`

The `SemidirectProduct.lift` of the two transports.  Given the lift compatibility (`hcompatLift`,
built by the caller from the `(9.7.b)` `C`-equivariance of the field iso) and the disjointness
`E ⊓ C = ⊥`, the embedding `σ` is injective and carries the additive kernel onto `E` and the
complement onto `C`.  Generic version of the `fieldNormalizerData_of_repr` assembly. -/

/-- **Lift compatibility from textbook equivariance.**  The `SemidirectProduct.lift` compatibility
`hcompatLift` demanded by `fieldModelEmbedding`, derived from the textbook `C`-conjugation
equivariance of the field iso — `e (ofMul (v x v⁻¹)) = μ v • e (ofMul x)` for `v ∈ C`, `x ∈ E`
(Peterfalvi `(14.2)(a)`).  Both sides (`S` = `P`/`U`, `T` = `Q`/`V`) route their `hcompatLift`
through this generic bridge; it transports the conjugation identity across the field iso `e` and
the `μ`-inversion inside `complementTransport`. -/
theorem hcompatLift_of_equivariant {r s : ℕ} [Fact r.Prime] {E C : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s)
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s)
    (hCE : ∀ (v : ↥C) (x : ↥E), (v : G) * (x : G) * (v : G)⁻¹ ∈ E)
    (hcompat : ∀ (v : ↥C) (x : ↥E),
      e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E))
        = ((μ v : (GaloisField r s)ˣ) : GaloisField r s) * e (Additive.ofMul x)) :
    ∀ u : ↥(normOneUnits r s),
      (kernelTransport e).comp ((normOneMulAction r s u).toMonoidHom)
        = (MulAut.conj (complementTransport μ hμ_inj hμ_range u)).toMonoidHom.comp
            (kernelTransport e) := by
  intro u
  ext s'
  obtain ⟨v, hμv, hfUv⟩ := complementTransport_exists μ hμ_inj hμ_range u
  change kernelTransport e ((normOneMulAction r s u) s') =
    complementTransport μ hμ_inj hμ_range u * kernelTransport e s' *
      (complementTransport μ hμ_inj hμ_range u)⁻¹
  rw [hfUv]
  have hact : (normOneMulAction r s u) s' =
      Multiplicative.ofAdd (((u : (GaloisField r s)ˣ) : GaloisField r s) *
          (Multiplicative.toAdd s' : GaloisField r s)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    conv_lhs => rw [← ofAdd_toAdd s']
    exact normOneMulAction_apply r s u (Multiplicative.toAdd s')
  rw [hact, kernelTransport_apply, kernelTransport_apply, toAdd_ofAdd]
  set t : GaloisField r s := Multiplicative.toAdd s' with htdef
  set x : ↥E := Additive.toMul (e.symm t) with hxdef
  have hex : e (Additive.ofMul x) = t := by
    rw [hxdef, ofMul_toMul, e.apply_symm_apply]
  have hkey : Additive.toMul (e.symm (((u : (GaloisField r s)ˣ) : GaloisField r s) * t)) =
      (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E) := by
    have h1 := hcompat v x
    rw [hex] at h1
    have hμvF : ((μ v : (GaloisField r s)ˣ) : GaloisField r s) =
        ((u : (GaloisField r s)ˣ) : GaloisField r s) := by rw [hμv]
    rw [hμvF] at h1
    have h2 : Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E) =
        e.symm (((u : (GaloisField r s)ˣ) : GaloisField r s) * t) := by
      rw [← h1, e.symm_apply_apply]
    rw [← h2, toMul_ofMul]
  rw [hkey]

/-- **Generic field-model embedding.**  From a field iso `e`, a norm-one character `μ` of the
complement, the lift compatibility, and disjointness `E ⊓ C = ⊥`, produce an injective
`σ : normOneFrobeniusGroup r s →* G` with additive kernel `↦ E` and complement `↦ C`. -/
theorem fieldModelEmbedding {r s : ℕ} [Fact r.Prime] {E C : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s)
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s)
    (hcompatLift : ∀ u : ↥(normOneUnits r s),
      (kernelTransport e).comp ((normOneMulAction r s u).toMonoidHom)
        = (MulAut.conj (complementTransport μ hμ_inj hμ_range u)).toMonoidHom.comp
            (kernelTransport e))
    (hEC_disj : E ⊓ C = ⊥) :
    ∃ σ : normOneFrobeniusGroup r s →* G,
      Function.Injective σ ∧
      (SemidirectProduct.inl :
          additiveFieldGroup r s →* normOneFrobeniusGroup r s).range.map σ = E ∧
      (SemidirectProduct.inr :
          ↥(normOneUnits r s) →* normOneFrobeniusGroup r s).range.map σ = C := by
  set sigma := SemidirectProduct.lift (kernelTransport e) (complementTransport μ hμ_inj hμ_range)
    hcompatLift with hsigma
  have hlift_apply : ∀ g : normOneFrobeniusGroup r s,
      sigma g = kernelTransport e g.left * complementTransport μ hμ_inj hμ_range g.right := by
    intro g
    rw [hsigma]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [map_mul, SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  refine ⟨sigma, ?_, ?_, ?_⟩
  · -- injective: `E ⊓ C = ⊥`
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker, hlift_apply] at hg
    have hmemE : kernelTransport e g.left ∈ E := by
      have h : kernelTransport e g.left ∈ (kernelTransport e).range := ⟨g.left, rfl⟩
      rwa [kernelTransport_range e] at h
    have hinv : kernelTransport e g.left = (complementTransport μ hμ_inj hμ_range g.right)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp hg
    have hmemC : kernelTransport e g.left ∈ C := by
      rw [hinv]; apply Subgroup.inv_mem
      have h : complementTransport μ hμ_inj hμ_range g.right ∈
          (complementTransport μ hμ_inj hμ_range).range := ⟨g.right, rfl⟩
      rwa [complementTransport_range μ hμ_inj hμ_range] at h
    have hbot : kernelTransport e g.left = 1 := by
      have hmem : kernelTransport e g.left ∈ E ⊓ C := ⟨hmemE, hmemC⟩
      rw [hEC_disj] at hmem; simpa using hmem
    have hleft : g.left = 1 := kernelTransport_injective e (by rw [hbot, map_one])
    have hcone : complementTransport μ hμ_inj hμ_range g.right = 1 := by
      have hg' := hg; rw [hbot, one_mul] at hg'; exact hg'
    have hright : g.right = 1 :=
      complementTransport_injective μ hμ_inj hμ_range (by rw [hcone, map_one])
    rw [Subgroup.mem_bot]; exact SemidirectProduct.ext hleft hright
  · -- additive kernel `↦ E`
    apply le_antisymm
    · rintro _ ⟨x, ⟨a, rfl⟩, rfl⟩
      have h : sigma (SemidirectProduct.inl a) = kernelTransport e a := by
        rw [hlift_apply]; simp
      have hmem : kernelTransport e a ∈ (kernelTransport e).range := ⟨a, rfl⟩
      rw [h]; rwa [kernelTransport_range e] at hmem
    · intro y hy
      have hy' : y ∈ (kernelTransport e).range := by rwa [kernelTransport_range e]
      obtain ⟨a, rfl⟩ := hy'
      refine ⟨SemidirectProduct.inl a, ⟨a, rfl⟩, ?_⟩
      rw [hlift_apply]; simp
  · -- complement `↦ C`
    apply le_antisymm
    · rintro _ ⟨x, ⟨b, rfl⟩, rfl⟩
      have h : sigma (SemidirectProduct.inr b) = complementTransport μ hμ_inj hμ_range b := by
        rw [hlift_apply]; simp
      have hmem : complementTransport μ hμ_inj hμ_range b ∈
          (complementTransport μ hμ_inj hμ_range).range := ⟨b, rfl⟩
      rw [h]; rwa [complementTransport_range μ hμ_inj hμ_range] at hmem
    · intro y hy
      have hy' : y ∈ (complementTransport μ hμ_inj hμ_range).range := by
        rwa [complementTransport_range μ hμ_inj hμ_range]
      obtain ⟨b, rfl⟩ := hy'
      refine ⟨SemidirectProduct.inr b, ⟨b, rfl⟩, ?_⟩
      rw [hlift_apply]; simp

end OddOrder.RepresentationTheory.SemilinearFieldModel
