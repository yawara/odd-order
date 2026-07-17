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

end OddOrder.Peterfalvi.Appendices.Suzuki
