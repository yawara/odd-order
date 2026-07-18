/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearModel

/-!
# Peterfalvi Part II, Chapter I §2 — reassociating the semilinear product

This file supplies the group-theoretic reassociation used in Proposition 3 (p. 104):
an action by `T ⋊ V` turns `E ⋊ (T ⋊ V)` into `(E ⋊ T) ⋊ V`, and compatible
coordinate equivalences transport the result to `𝓛(F, A)`.
-/

namespace SemidirectProduct

universe uE uT uV uD

section Reassociation

variable {E : Type uE} {T : Type uT} {V : Type uV}
  [Group E] [Group T] [Group V]
  (κ : V →* MulAut T) (α : (T ⋊[κ] V) →* MulAut E)

/-- The restriction to the left factor of an action by a semidirect product. -/
def leftFactorAction : T →* MulAut E :=
  α.comp SemidirectProduct.inl

/-- The restriction to the right factor of an action by a semidirect product. -/
def rightFactorAction : V →* MulAut E :=
  α.comp SemidirectProduct.inr

/-- The right factor acts componentwise on the semidirect product of `E` by `T`. -/
def rightFactorActionOnLeftSemidirect :
    V →* MulAut (E ⋊[leftFactorAction κ α] T) where
  toFun v :=
    SemidirectProduct.congr (rightFactorAction κ α v) (κ v) (fun t => by
      ext e
      change α (SemidirectProduct.inr v) (α (SemidirectProduct.inl t) e) =
        α (SemidirectProduct.inl (κ v t)) (α (SemidirectProduct.inr v) e)
      have h :
          (SemidirectProduct.inr v : T ⋊[κ] V) * SemidirectProduct.inl t =
            SemidirectProduct.inl (κ v t) * SemidirectProduct.inr v := by
        rw [SemidirectProduct.inl_aut]
        simp [mul_assoc]
      calc
        α (SemidirectProduct.inr v) (α (SemidirectProduct.inl t) e) =
            α (SemidirectProduct.inr v * SemidirectProduct.inl t) e := by
              rw [map_mul]
              rfl
        _ = α (SemidirectProduct.inl (κ v t) * SemidirectProduct.inr v) e := by rw [h]
        _ = α (SemidirectProduct.inl (κ v t)) (α (SemidirectProduct.inr v) e) := by
              rw [map_mul]
              rfl)
  map_one' := by ext <;> simp [rightFactorAction]
  map_mul' v w := by ext <;> simp [rightFactorAction]

/-- Reassociate a semidirect product by a semidirect product. -/
def reassoc :
    E ⋊[α] (T ⋊[κ] V) ≃*
      (E ⋊[leftFactorAction κ α] T) ⋊[rightFactorActionOnLeftSemidirect κ α] V where
  toFun x := ⟨⟨x.left, x.right.left⟩, x.right.right⟩
  invFun x := ⟨x.left.left, ⟨x.left.right, x.right⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext
      · change x.left * α x.right y.left =
          x.left * α (SemidirectProduct.inl x.right.left)
            (α (SemidirectProduct.inr x.right.right) y.left)
        congr 1
        rw [← MulAut.mul_apply, ← map_mul, SemidirectProduct.inl_left_mul_inr_right]
      · rfl
    · rfl

end Reassociation

section Transport

variable {E : Type uE} {T : Type uT} {V : Type uV} {D : Type uD}
  [Group E] [Group T] [Group V] [Group D]
  (κ : V →* MulAut T) (α : D →* MulAut E)
  (δ : T ⋊[κ] V ≃* D)

/-- Reassociate after transporting the acting group across a semidirect decomposition. -/
def reassocOfEquiv :
    E ⋊[α] D ≃*
      (E ⋊[leftFactorAction κ (α.comp δ.toMonoidHom)] T) ⋊[
        rightFactorActionOnLeftSemidirect κ (α.comp δ.toMonoidHom)] V :=
  (SemidirectProduct.congr (MulEquiv.refl E) δ (fun _ => by ext; rfl)).symm.trans
    (reassoc κ (α.comp δ.toMonoidHom))

end Transport

end SemidirectProduct

namespace OddOrder.Peterfalvi.Appendices.Suzuki

universe uE uT uV uD uF

section SemilinearTransport

variable {E : Type uE} {T : Type uT} {V : Type uV} {D : Type uD}
  [Group E] [Group T] [Group V] [Group D]
  {F : Type uF} [Field F] (A : Subgroup (RingAut F))
  (κ : V →* MulAut T) (α : D →* MulAut E)
  (δ : T ⋊[κ] V ≃* D)
  (e : E ≃* Multiplicative F) (μ : T ≃* Fˣ) (ν : V ≃* A)

/-- Transport a reassociated semidirect product to the semilinear affine group. -/
def SemidirectProduct.reassocOfEquivToSemilinear
    (hT : ∀ t : T,
      (SemidirectProduct.leftFactorAction κ (α.comp δ.toMonoidHom) t).trans e =
        e.trans (fieldScalarAction F (μ t)))
    (hE : ∀ v : V,
      (SemidirectProduct.rightFactorAction κ (α.comp δ.toMonoidHom) v).trans e =
        e.trans (fieldRingAutOnAdditive F (ν v : RingAut F)))
    (hκ : ∀ v : V,
      (κ v).trans μ = μ.trans (fieldRingAutOnUnits F (ν v : RingAut F))) :
    E ⋊[α] D ≃* semilinearGroup F A :=
  (SemidirectProduct.reassocOfEquiv κ α δ).trans <|
    SemidirectProduct.congr (SemidirectProduct.congr e μ hT) ν (fun v => by
      ext x <;>
        simp only [SemidirectProduct.rightFactorActionOnLeftSemidirect,
          SemidirectProduct.congr_apply_left, SemidirectProduct.congr_apply_right,
          MulEquiv.trans_apply]
      · exact DFunLike.congr_fun (hE v) x.left
      · exact congrArg (fun u : Fˣ => (u : F))
          (DFunLike.congr_fun (hκ v) x.right))

end SemilinearTransport

section ComponentImages

variable {E : Type uE} {T : Type uT} {V : Type uV} {D : Type uD}
  [Group E] [Group T] [Group V] [Group D]
  {F : Type uF} [Field F] (A : Subgroup (RingAut F))
  (κ : V →* MulAut T) (α : D →* MulAut E)
  (δ : T ⋊[κ] V ≃* D)
  (e : E ≃* Multiplicative F) (μ : T ≃* Fˣ) (ν : V ≃* A)
  (hT : ∀ t : T,
    (SemidirectProduct.leftFactorAction κ (α.comp δ.toMonoidHom) t).trans e =
      e.trans (fieldScalarAction F (μ t)))
  (hE : ∀ v : V,
    (SemidirectProduct.rightFactorAction κ (α.comp δ.toMonoidHom) v).trans e =
      e.trans (fieldRingAutOnAdditive F (ν v : RingAut F)))
  (hκ : ∀ v : V,
    (κ v).trans μ = μ.trans (fieldRingAutOnUnits F (ν v : RingAut F)))

local notation "Φ" => SemidirectProduct.reassocOfEquivToSemilinear
  A κ α δ e μ ν hT hE hκ

/-- The semilinear reassociation sends the normal factor to the additive-field factor. -/
theorem reassocOfEquivToSemilinear_inl (x : E) :
    Φ (SemidirectProduct.inl x) =
      SemidirectProduct.inl (SemidirectProduct.inl (e x)) := by
  let c₀ := SemidirectProduct.congr
    (φ₁ := α.comp δ.toMonoidHom) (φ₂ := α)
    (MulEquiv.refl E) δ (fun _ => by ext; rfl)
  let c₂ :
      (E ⋊[SemidirectProduct.leftFactorAction κ (α.comp δ.toMonoidHom)] T) ⋊[
        SemidirectProduct.rightFactorActionOnLeftSemidirect κ
          (α.comp δ.toMonoidHom)] V ≃* semilinearGroup F A :=
    SemidirectProduct.congr (SemidirectProduct.congr e μ hT) ν (fun v => by
    ext y <;>
      simp only [SemidirectProduct.rightFactorActionOnLeftSemidirect,
        SemidirectProduct.congr_apply_left, SemidirectProduct.congr_apply_right,
        MulEquiv.trans_apply]
    · exact DFunLike.congr_fun (hE v) y.left
    · exact congrArg (fun u : Fˣ => (u : F))
        (DFunLike.congr_fun (hκ v) y.right))
  have hc : c₀.symm (SemidirectProduct.inl x : E ⋊[α] D) =
      (SemidirectProduct.inl x : E ⋊[α.comp δ.toMonoidHom] (T ⋊[κ] V)) := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.congr_symm_apply_left]
      rfl
    · rw [SemidirectProduct.congr_symm_apply_right]
      change δ.symm 1 = 1
      exact map_one δ.symm
  change c₂ (SemidirectProduct.reassoc κ (α.comp δ.toMonoidHom)
      (c₀.symm (SemidirectProduct.inl x))) = _
  rw [hc]
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · change e x = e x
      rfl
    · change μ 1 = 1
      exact map_one μ
  · change ν 1 = 1
    exact map_one ν

/-- The semilinear reassociation sends the left acting factor to the scalar factor. -/
theorem reassocOfEquivToSemilinear_leftFactor (t : T) :
    Φ (SemidirectProduct.inr (δ (SemidirectProduct.inl t))) =
      SemidirectProduct.inl (SemidirectProduct.inr (μ t)) := by
  let c₀ := SemidirectProduct.congr
    (φ₁ := α.comp δ.toMonoidHom) (φ₂ := α)
    (MulEquiv.refl E) δ (fun _ => by ext; rfl)
  let c₂ :
      (E ⋊[SemidirectProduct.leftFactorAction κ (α.comp δ.toMonoidHom)] T) ⋊[
        SemidirectProduct.rightFactorActionOnLeftSemidirect κ
          (α.comp δ.toMonoidHom)] V ≃* semilinearGroup F A :=
    SemidirectProduct.congr (SemidirectProduct.congr e μ hT) ν (fun v => by
      ext y <;>
        simp only [SemidirectProduct.rightFactorActionOnLeftSemidirect,
          SemidirectProduct.congr_apply_left, SemidirectProduct.congr_apply_right,
          MulEquiv.trans_apply]
      · exact DFunLike.congr_fun (hE v) y.left
      · exact congrArg (fun u : Fˣ => (u : F))
          (DFunLike.congr_fun (hκ v) y.right))
  have hc : c₀.symm
      (SemidirectProduct.inr (δ (SemidirectProduct.inl t)) : E ⋊[α] D) =
      (SemidirectProduct.inr (SemidirectProduct.inl t) :
        E ⋊[α.comp δ.toMonoidHom] (T ⋊[κ] V)) := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.congr_symm_apply_left]
      rfl
    · rw [SemidirectProduct.congr_symm_apply_right]
      change δ.symm (δ (SemidirectProduct.inl t)) = SemidirectProduct.inl t
      exact δ.symm_apply_apply _
  change c₂ (SemidirectProduct.reassoc κ (α.comp δ.toMonoidHom)
      (c₀.symm (SemidirectProduct.inr (δ (SemidirectProduct.inl t))))) = _
  rw [hc]
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · change e 1 = 1
      exact map_one e
    · change μ t = μ t
      rfl
  · change ν 1 = 1
    exact map_one ν

/-- The semilinear reassociation sends the right acting factor to the
field-automorphism factor. -/
theorem reassocOfEquivToSemilinear_rightFactor (v : V) :
    Φ (SemidirectProduct.inr (δ (SemidirectProduct.inr v))) =
      SemidirectProduct.inr (ν v) := by
  let c₀ := SemidirectProduct.congr
    (φ₁ := α.comp δ.toMonoidHom) (φ₂ := α)
    (MulEquiv.refl E) δ (fun _ => by ext; rfl)
  let c₂ :
      (E ⋊[SemidirectProduct.leftFactorAction κ (α.comp δ.toMonoidHom)] T) ⋊[
        SemidirectProduct.rightFactorActionOnLeftSemidirect κ
          (α.comp δ.toMonoidHom)] V ≃* semilinearGroup F A :=
    SemidirectProduct.congr (SemidirectProduct.congr e μ hT) ν (fun z => by
      ext y <;>
        simp only [SemidirectProduct.rightFactorActionOnLeftSemidirect,
          SemidirectProduct.congr_apply_left, SemidirectProduct.congr_apply_right,
          MulEquiv.trans_apply]
      · exact DFunLike.congr_fun (hE z) y.left
      · exact congrArg (fun u : Fˣ => (u : F))
          (DFunLike.congr_fun (hκ z) y.right))
  have hc : c₀.symm
      (SemidirectProduct.inr (δ (SemidirectProduct.inr v)) : E ⋊[α] D) =
      (SemidirectProduct.inr (SemidirectProduct.inr v) :
        E ⋊[α.comp δ.toMonoidHom] (T ⋊[κ] V)) := by
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.congr_symm_apply_left]
      rfl
    · rw [SemidirectProduct.congr_symm_apply_right]
      change δ.symm (δ (SemidirectProduct.inr v)) = SemidirectProduct.inr v
      exact δ.symm_apply_apply _
  change c₂ (SemidirectProduct.reassoc κ (α.comp δ.toMonoidHom)
      (c₀.symm (SemidirectProduct.inr (δ (SemidirectProduct.inr v))))) = _
  rw [hc]
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · change e 1 = 1
      exact map_one e
    · change μ 1 = 1
      exact map_one μ
  · change ν v = ν v
    rfl

end ComponentImages

end OddOrder.Peterfalvi.Appendices.Suzuki
