/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearIdentification
import OddOrder.Peterfalvi.Appendices.Suzuki.SemidirectReassociation
import OddOrder.Peterfalvi.Appendices.SemilinearField

/-!
# Peterfalvi Part II, Chapter I §2, Proposition 3 — semilinear realization

The first stage of Proposition 3 (p. 104) identifies the Fitting complement acting on
`Q₀` with the full multiplicative group of a finite field of order `|Q₀|`, and chooses
the distinguished involution as the additive coordinate `1`.
-/

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.Isaacs.Ch01 (fitting)
open OddOrder.Peterfalvi.Appendices.Huppert

namespace Hypothesis

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω)

local instance : CommGroup ↥hyp.Q0 :=
  { (inferInstance : Group ↥hyp.Q0) with
    mul_comm := fun x y => Subtype.ext (hyp.commute_of_mem_Q0 x.2 y.2).eq }

/-- **Peterfalvi Part II, Chapter I §2, Proposition 3 (field-scalar part).**
The irreducible fixed-point-free Fitting action constructs a finite field `F` of order
`|Q₀|` and identifies `F(D̄)` with every nonzero scalar of `F`.  The final clause retains
the normalizer-semilinearity supplied by Huppert Appendix I, Proposition 2(b). -/
theorem exists_fitting_field_model :
    ∃ (F : Type u) (_ : Field F) (_ : Module F (Additive ↥hyp.Q0)) (_ : Finite F),
      Module.finrank F (Additive ↥hyp.Q0) = 1 ∧
      Nat.card F = Nat.card ↥hyp.Q0 ∧
      (∃ μ : ↥(fitting hyp.Dbar) ≃* Fˣ,
        ∀ (t : ↥(fitting hyp.Dbar)) (x : Additive ↥hyp.Q0),
          ((μ t : Fˣ) : F) • x =
            Additive.ofMul (hyp.fittingAction t (Additive.toMul x))) ∧
      ∀ (g : MulAut ↥hyp.Q0) (c : ↥(fitting hyp.Dbar) ≃* ↥(fitting hyp.Dbar)),
        (∀ t, hyp.fittingAction (c t) =
          g * hyp.fittingAction t * g⁻¹) →
          ∃ σ : F ≃+* F, ∀ (a : F) (x : Additive ↥hyp.Q0),
            (MulEquiv.toAdditive g) (a • x) =
              σ a • (MulEquiv.toAdditive g) x := by
  letI : IsCyclic ↥(fitting hyp.Dbar) := hyp.fitting_Dbar_cyclic_fpf_abelian.1
  letI : CommGroup ↥(fitting hyp.Dbar) := IsCyclic.commGroup
  obtain ⟨F, hFfield, hFmodule, hFfinite, hdim, hcard, ⟨μ, hμ⟩, hsemi⟩ :=
    exists_field_semilinear_with_scalar hyp.isElementaryAbelian_Q0
      hyp.fittingAction hyp.fittingAction_irreducible
  letI : Field F := hFfield
  letI : Module F (Additive ↥hyp.Q0) := hFmodule
  letI : Finite F := hFfinite
  have hμinj : Function.Injective μ := by
    apply (injective_iff_map_eq_one μ).2
    intro t ht
    apply Subtype.ext
    apply hyp.injective_conjQ0bar
    apply MulEquiv.ext
    intro x
    apply Additive.ofMul.injective
    have hs := hμ t (Additive.ofMul x)
    rw [ht] at hs
    simpa [fittingAction] using hs.symm
  have hs0 : Additive.ofMul hyp.sQ0 ≠ 0 := by
    intro hs
    apply hyp.sQ0_ne_one
    apply Additive.ofMul.injective
    simpa using hs
  have hμsurj : Function.Surjective μ := by
    intro a
    let yA : Additive ↥hyp.Q0 := (a : F) • Additive.ofMul hyp.sQ0
    have hyA0 : yA ≠ 0 := by
      exact smul_ne_zero (Units.ne_zero a) hs0
    let y : ↥hyp.Q0 := Additive.toMul yA
    have hy1 : y ≠ 1 := by
      intro hy
      apply hyA0
      apply Additive.toMul.injective
      simpa [y] using hy
    obtain ⟨t, ht⟩ := hyp.fittingAction_transitive hyp.sQ0 y
      hyp.sQ0_ne_one hy1
    refine ⟨t, ?_⟩
    apply Units.ext
    apply smul_left_injective F hs0
    have hscalar : ((μ t : Fˣ) : F) • Additive.ofMul hyp.sQ0 =
        Additive.ofMul (hyp.fittingAction t hyp.sQ0) := by
      simpa using hμ t (Additive.ofMul hyp.sQ0)
    rw [ht] at hscalar
    simpa [y, yA] using hscalar
  let μe : ↥(fitting hyp.Dbar) ≃* Fˣ := MulEquiv.ofBijective μ ⟨hμinj, hμsurj⟩
  exact ⟨F, hFfield, hFmodule, hFfinite, hdim, hcard, ⟨μe, hμ⟩, hsemi⟩

/-- In the one-dimensional field model, evaluation at the distinguished involution
identifies the additive group of `Q₀` with the additive group of the field. -/
theorem exists_sQ0_addEquiv_of_finrank_one {F : Type u} [Field F] [Module F (Additive ↥hyp.Q0)]
    (hdim : Module.finrank F (Additive ↥hyp.Q0) = 1) :
    ∃ e : Additive ↥hyp.Q0 ≃+ F,
      ∀ a : F, e.symm a = a • Additive.ofMul hyp.sQ0 := by
  let s : Additive ↥hyp.Q0 := Additive.ofMul hyp.sQ0
  have hs0 : s ≠ 0 := by
    intro hs
    apply hyp.sQ0_ne_one
    apply Additive.ofMul.injective
    simpa [s] using hs
  let toLine : F →ₗ[F] Additive ↥hyp.Q0 :=
    LinearMap.toSpanSingleton F (Additive ↥hyp.Q0) s
  have hinj : Function.Injective toLine := by
    intro a b hab
    apply smul_left_injective F hs0
    simpa [toLine, LinearMap.toSpanSingleton_apply] using hab
  have hsurj : Function.Surjective toLine := by
    intro x
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hs0 x
    exact ⟨a, by simpa [toLine, LinearMap.toSpanSingleton_apply] using ha⟩
  let eLin : F ≃ₗ[F] Additive ↥hyp.Q0 :=
    LinearEquiv.ofBijective toLine ⟨hinj, hsurj⟩
  refine ⟨eLin.symm.toAddEquiv, fun a => ?_⟩
  change eLin a = a • Additive.ofMul hyp.sQ0
  rfl

/-- The action of the point stabilizer `V̄` on `Q₀`. -/
def VbarAction : ↥hyp.Vbar →* MulAut ↥hyp.Q0 :=
  hyp.conjQ0bar.comp hyp.Vbar.subtype

/-- Conjugation by `V̄` on the normal Fitting subgroup. -/
abbrev fittingConjAction : ↥hyp.Vbar →* MulAut ↥(fitting hyp.Dbar) :=
  (fitting hyp.Dbar).normalizerMonoidHom.comp
    (Subgroup.inclusion ((fitting hyp.Dbar).normalizer_eq_top ▸ le_top))

/-- The action on `Q₀` intertwines conjugation of `F(D̄)` by `V̄`. -/
theorem fittingAction_fittingConjAction
    (z : ↥hyp.Vbar) (t : ↥(fitting hyp.Dbar)) :
    hyp.fittingAction (hyp.fittingConjAction z t) =
      hyp.VbarAction z * hyp.fittingAction t * (hyp.VbarAction z)⁻¹ := by
  ext q
  simp [fittingAction, VbarAction,
    Subgroup.normalizerMonoidHom_apply_apply_coe]

/-- Every member of `V̄` fixes the distinguished point. -/
theorem VbarAction_fix_sQ0 (z : ↥hyp.Vbar) :
    hyp.VbarAction z hyp.sQ0 = hyp.sQ0 := by
  change hyp.conjQ0bar (z : hyp.Dbar) hyp.sQ0 = hyp.sQ0
  have hz : (z : hyp.Dbar) ∈
      OddOrder.Peterfalvi.Appendices.Huppert.pointStabilizer
        hyp.conjQ0bar hyp.sQ0 := by
    rw [← hyp.Vbar_eq_pointStabilizer]
    exact z.2
  exact OddOrder.Peterfalvi.Appendices.Huppert.mem_pointStabilizer.mp hz

/-- Scalar realization and the semilinear companion respect the conjugation action. -/
theorem fittingScalar_companion_compat
    {F : Type u} [Field F] [Module F (Additive ↥hyp.Q0)]
    (μ : ↥(fitting hyp.Dbar) ≃* Fˣ)
    (hμ : ∀ (t : ↥(fitting hyp.Dbar)) (x : Additive ↥hyp.Q0),
      ((μ t : Fˣ) : F) • x =
        Additive.ofMul (hyp.fittingAction t (Additive.toMul x)))
    (ν : ↥hyp.Vbar →* (F ≃+* F))
    (hνsemi : ∀ (z : ↥hyp.Vbar) (a : F) (x : Additive ↥hyp.Q0),
      (MulEquiv.toAdditive (hyp.VbarAction z)) (a • x) =
        ν z a • (MulEquiv.toAdditive (hyp.VbarAction z)) x)
    (z : ↥hyp.Vbar) (t : ↥(fitting hyp.Dbar)) :
    μ (hyp.fittingConjAction z t) =
      fieldRingAutOnUnits F (ν z) (μ t) := by
  let s : Additive ↥hyp.Q0 := Additive.ofMul hyp.sQ0
  have hs0 : s ≠ 0 := by
    intro hs
    apply hyp.sQ0_ne_one
    apply Additive.ofMul.injective
    simpa [s] using hs
  have hfix : hyp.VbarAction z hyp.sQ0 = hyp.sQ0 :=
    hyp.VbarAction_fix_sQ0 z
  have hfix_inv : (hyp.VbarAction z)⁻¹ hyp.sQ0 = hyp.sQ0 := by
    have h := congrArg (hyp.VbarAction z).symm hfix
    simpa using h.symm
  apply Units.ext
  apply smul_left_injective F hs0
  calc
    ((μ (hyp.fittingConjAction z t) : Fˣ) : F) • s =
        Additive.ofMul
          (hyp.fittingAction (hyp.fittingConjAction z t) hyp.sQ0) := by
            simpa [s] using hμ (hyp.fittingConjAction z t) s
    _ = (MulEquiv.toAdditive (hyp.VbarAction z))
          (Additive.ofMul (hyp.fittingAction t hyp.sQ0)) := by
            rw [hyp.fittingAction_fittingConjAction z t]
            change Additive.ofMul
                (hyp.VbarAction z
                  (hyp.fittingAction t ((hyp.VbarAction z)⁻¹ hyp.sQ0))) =
              Additive.ofMul (hyp.VbarAction z (hyp.fittingAction t hyp.sQ0))
            rw [hfix_inv]
    _ = (MulEquiv.toAdditive (hyp.VbarAction z))
          (((μ t : Fˣ) : F) • s) := by
            rw [hμ t s]
            rfl
    _ = ν z ((μ t : Fˣ) : F) •
          (MulEquiv.toAdditive (hyp.VbarAction z)) s :=
            hνsemi z ((μ t : Fˣ) : F) s
    _ = ν z ((μ t : Fˣ) : F) • s := by
          change ν z ((μ t : Fˣ) : F) •
              Additive.ofMul (hyp.VbarAction z hyp.sQ0) = _
          rw [hfix]
    _ = (((fieldRingAutOnUnits F (ν z)) (μ t) : Fˣ) : F) • s := by
          rw [fieldRingAutOnUnits_apply_val]

/-- **Peterfalvi Part II, Chapter I §2, Proposition 3 (semilinear data).**
There is one finite field model in which `F(D̄)` is the full scalar group,
`V̄` is a subgroup of `Aut(F)`, and both actions are compatible. -/
theorem exists_semilinear_field_model :
    ∃ (F : Type u) (_ : Field F) (_ : Module F (Additive ↥hyp.Q0))
      (_ : Finite F),
      Module.finrank F (Additive ↥hyp.Q0) = 1 ∧
      Nat.card F = Nat.card ↥hyp.Q0 ∧
      ∃ (μ : ↥(fitting hyp.Dbar) ≃* Fˣ)
        (ν : ↥hyp.Vbar →* (F ≃+* F))
        (νe : ↥hyp.Vbar ≃* ↥(MonoidHom.range ν)),
        Function.Injective ν ∧
        (∀ (t : ↥(fitting hyp.Dbar)) (x : Additive ↥hyp.Q0),
          ((μ t : Fˣ) : F) • x =
            Additive.ofMul (hyp.fittingAction t (Additive.toMul x))) ∧
        (∀ (z : ↥hyp.Vbar) (a : F) (x : Additive ↥hyp.Q0),
          (MulEquiv.toAdditive (hyp.VbarAction z)) (a • x) =
            ν z a • (MulEquiv.toAdditive (hyp.VbarAction z)) x) ∧
        (∀ z, (νe z : F ≃+* F) = ν z) ∧
        ∀ (z : ↥hyp.Vbar) (t : ↥(fitting hyp.Dbar)),
          μ (hyp.fittingConjAction z t) =
            fieldRingAutOnUnits F (ν z) (μ t) := by
  obtain ⟨F, hF, hmodule, hfinite, hdim, hcard, ⟨μ, hμ⟩, hsemilinear⟩ :=
    hyp.exists_fitting_field_model
  letI : Field F := hF
  letI : Module F (Additive ↥hyp.Q0) := hmodule
  letI : Finite F := hfinite
  have hfix : ∀ z : ↥hyp.Vbar, hyp.VbarAction z hyp.sQ0 = hyp.sQ0 :=
    hyp.VbarAction_fix_sQ0
  have hrho : Function.Injective hyp.VbarAction :=
    hyp.injective_conjQ0bar.comp Subtype.val_injective
  have hsemi : ∀ z : ↥hyp.Vbar, ∃ σ : F ≃+* F,
      ∀ (a : F) (x : Additive ↥hyp.Q0),
        (MulEquiv.toAdditive (hyp.VbarAction z)) (a • x) =
          σ a • (MulEquiv.toAdditive (hyp.VbarAction z)) x := by
    intro z
    exact hsemilinear (hyp.VbarAction z) (hyp.fittingConjAction z)
      (hyp.fittingAction_fittingConjAction z)
  obtain ⟨ν, hν, hνsemi⟩ :=
    OddOrder.Peterfalvi.Appendices.Huppert.exists_injective_semilinear_companion
      hyp.VbarAction hyp.sQ0 hyp.sQ0_ne_one hdim hfix hrho hsemi
  let νe : ↥hyp.Vbar ≃* ↥(MonoidHom.range ν) :=
    MulEquiv.ofBijective ν.rangeRestrict
      ⟨fun _ _ h ↦ hν (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective ν⟩
  refine ⟨F, hF, hmodule, hfinite, hdim, hcard, μ, ν, νe,
    hν, hμ, hνsemi, fun _ ↦ rfl, ?_⟩
  exact hyp.fittingScalar_companion_compat μ hμ ν hνsemi

/-- The complementary subgroups `F(D̄)` and `V̄` give the external decomposition of `D̄`. -/
noncomputable def fittingSemidirectEquiv :
    ↥(fitting hyp.Dbar) ⋊[hyp.fittingConjAction] ↥hyp.Vbar ≃* hyp.Dbar :=
  SemidirectProduct.mulEquivSubgroup hyp.fitting_isComplement_Vbar

/-- The scalar and field-automorphism coordinates intertwine all three actions in the
reassociated semidirect product used by Proposition 3. -/
theorem exists_equivariant_field_coordinates
    {F : Type u} [Field F] [Module F (Additive ↥hyp.Q0)]
    (hdim : Module.finrank F (Additive ↥hyp.Q0) = 1)
    (μ : ↥(fitting hyp.Dbar) ≃* Fˣ)
    (ν : ↥hyp.Vbar →* (F ≃+* F))
    (νe : ↥hyp.Vbar ≃* ↥(MonoidHom.range ν))
    (hμ : ∀ (t : ↥(fitting hyp.Dbar)) (x : Additive ↥hyp.Q0),
      ((μ t : Fˣ) : F) • x =
        Additive.ofMul (hyp.fittingAction t (Additive.toMul x)))
    (hνsemi : ∀ (z : ↥hyp.Vbar) (a : F) (x : Additive ↥hyp.Q0),
      (MulEquiv.toAdditive (hyp.VbarAction z)) (a • x) =
        ν z a • (MulEquiv.toAdditive (hyp.VbarAction z)) x)
    (hνe : ∀ z, (νe z : F ≃+* F) = ν z)
    (hcompat : ∀ (z : ↥hyp.Vbar) (t : ↥(fitting hyp.Dbar)),
      μ (hyp.fittingConjAction z t) =
        fieldRingAutOnUnits F (ν z) (μ t)) :
    ∃ e : ↥hyp.Q0 ≃* Multiplicative F,
      (∀ t : ↥(fitting hyp.Dbar),
        (SemidirectProduct.leftFactorAction hyp.fittingConjAction
          (hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom) t).trans e =
            e.trans (fieldScalarAction F (μ t))) ∧
      (∀ z : ↥hyp.Vbar,
        (SemidirectProduct.rightFactorAction hyp.fittingConjAction
          (hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom) z).trans e =
            e.trans (fieldRingAutOnAdditive F (νe z : RingAut F))) ∧
      ∀ z : ↥hyp.Vbar,
        (hyp.fittingConjAction z).trans μ =
          μ.trans (fieldRingAutOnUnits F (νe z : RingAut F)) := by
  obtain ⟨eA, heA⟩ := hyp.exists_sQ0_addEquiv_of_finrank_one hdim
  let e : ↥hyp.Q0 ≃* Multiplicative F := AddEquiv.toMultiplicativeRight eA
  refine ⟨e, ?_, ?_, ?_⟩
  · intro t
    ext x
    apply Multiplicative.toAdd.injective
    change eA (Additive.ofMul
        ((hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom)
          (SemidirectProduct.inl t) x)) =
      ((μ t : Fˣ) : F) * eA (Additive.ofMul x)
    apply eA.symm.injective
    rw [eA.symm_apply_apply, heA, mul_smul, ← heA, eA.symm_apply_apply]
    simpa [fittingSemidirectEquiv, fittingAction] using
      (hμ t (Additive.ofMul x)).symm
  · intro z
    ext x
    apply Multiplicative.toAdd.injective
    change eA (Additive.ofMul
        ((hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom)
          (SemidirectProduct.inr z) x)) =
      (νe z : RingAut F) (eA (Additive.ofMul x))
    apply eA.symm.injective
    rw [eA.symm_apply_apply, heA, hνe]
    let a : F := eA (Additive.ofMul x)
    have hx : eA.symm a = Additive.ofMul x := eA.symm_apply_apply _
    have hz := hνsemi z a (Additive.ofMul hyp.sQ0)
    have hzfix :
        (MulEquiv.toAdditive (hyp.VbarAction z)) (Additive.ofMul hyp.sQ0) =
          Additive.ofMul hyp.sQ0 := by
      exact congrArg Additive.ofMul (hyp.VbarAction_fix_sQ0 z)
    rw [← heA, hx] at hz
    rw [hzfix] at hz
    simpa [fittingSemidirectEquiv, VbarAction] using hz
  · intro z
    apply MulEquiv.ext
    intro t
    change μ (hyp.fittingConjAction z t) =
      fieldRingAutOnUnits F (νe z : RingAut F) (μ t)
    rw [hνe]
    exact hcompat z t

/-- **Peterfalvi Part II, Chapter I §2, Proposition 3.**
The group on `Q0` and `Dbar` is a semilinear affine group over a finite field of
order `|Q0|`; its point-stabilizer factor `Vbar` is cyclic. -/
theorem exists_semilinear_equiv :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F)
      (A : Subgroup (RingAut F)),
      Nat.card F = Nat.card ↥hyp.Q0 ∧
      IsCyclic ↥hyp.Vbar ∧
      ∃ (eQ : ↥hyp.Q0 ≃* Multiplicative F)
        (μ : ↥(fitting hyp.Dbar) ≃* Fˣ)
        (νe : ↥hyp.Vbar ≃* A),
        (∀ t : ↥(fitting hyp.Dbar),
          (SemidirectProduct.leftFactorAction hyp.fittingConjAction
            (hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom) t).trans eQ =
              eQ.trans (fieldScalarAction F (μ t))) ∧
        (∀ z : ↥hyp.Vbar,
          (SemidirectProduct.rightFactorAction hyp.fittingConjAction
            (hyp.conjQ0bar.comp hyp.fittingSemidirectEquiv.toMonoidHom) z).trans eQ =
              eQ.trans (fieldRingAutOnAdditive F (νe z : RingAut F))) ∧
        (∀ z : ↥hyp.Vbar,
          (hyp.fittingConjAction z).trans μ =
            μ.trans (fieldRingAutOnUnits F (νe z : RingAut F))) ∧
        ∃ eL : ↥hyp.Q0 ⋊[hyp.conjQ0bar] hyp.Dbar ≃* semilinearGroup F A,
          (∀ q : ↥hyp.Q0,
            eL (SemidirectProduct.inl q) =
              SemidirectProduct.inl (SemidirectProduct.inl (eQ q))) ∧
          (∀ t : ↥(fitting hyp.Dbar),
            eL (SemidirectProduct.inr
                (hyp.fittingSemidirectEquiv (SemidirectProduct.inl t))) =
              SemidirectProduct.inl (SemidirectProduct.inr (μ t))) ∧
          ∀ z : ↥hyp.Vbar,
            eL (SemidirectProduct.inr
                (hyp.fittingSemidirectEquiv (SemidirectProduct.inr z))) =
              SemidirectProduct.inr (νe z) := by
  obtain ⟨F, hF, hmodule, hfinite, hdim, hcard,
      μ, ν, νe, _hνinj, hμ, hνsemi, hνe, hcompat⟩ :=
    hyp.exists_semilinear_field_model
  letI : Field F := hF
  letI : Module F (Additive ↥hyp.Q0) := hmodule
  letI : Finite F := hfinite
  let A : Subgroup (RingAut F) := MonoidHom.range ν
  have hVcyclic : IsCyclic ↥hyp.Vbar :=
    (νe.symm.isCyclic).mp (ringAutSubgroup_isCyclic_of_finite F A)
  obtain ⟨eQ, hT, hE, hκ⟩ :=
    hyp.exists_equivariant_field_coordinates hdim μ ν νe
      hμ hνsemi hνe hcompat
  let semilinearEquiv :
      ↥hyp.Q0 ⋊[hyp.conjQ0bar] hyp.Dbar ≃* semilinearGroup F A :=
    SemidirectProduct.reassocOfEquivToSemilinear A hyp.fittingConjAction
      hyp.conjQ0bar hyp.fittingSemidirectEquiv eQ μ νe hT hE hκ
  refine ⟨F, hF, hfinite, A, hcard, hVcyclic, eQ, μ, νe,
    hT, hE, hκ, semilinearEquiv, ?_, ?_, ?_⟩
  · intro q
    exact reassocOfEquivToSemilinear_inl A hyp.fittingConjAction
      hyp.conjQ0bar hyp.fittingSemidirectEquiv eQ μ νe hT hE hκ q
  · intro t
    exact reassocOfEquivToSemilinear_leftFactor A hyp.fittingConjAction
      hyp.conjQ0bar hyp.fittingSemidirectEquiv eQ μ νe hT hE hκ t
  · intro z
    exact reassocOfEquivToSemilinear_rightFactor A hyp.fittingConjAction
      hyp.conjQ0bar hyp.fittingSemidirectEquiv eQ μ νe hT hE hκ z

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
