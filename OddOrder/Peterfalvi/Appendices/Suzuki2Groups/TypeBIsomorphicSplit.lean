/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CentralExtensionAutomorphisms
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.Types
import OddOrder.Peterfalvi.Appendices.Suzuki2Groups.AutomorphismInducedMaps

/-!
# Peterfalvi Appendix III, Theorem (e), forward direction: setup

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix III, Theorem (e), p. 141 (issue 2052).

For the type-B model `B(n, φ, ε)` the theorem identifies the actor `K`
with `F*` acting *diagonally* on the quotient coordinate `F × F` —
`(a, b)^x = (xa, xb)` — and by `c^x = xφ(x)·c` on the center.  This file
constructs, for each `x ∈ F*`, an actual automorphism of the model
inducing that pair (`exists_diagonalAut`): the compatibility identity
`q(xa, xb) = xφ(x)·q(a, b)` of the type-B square map feeds the Lemma 1(c)
sufficiency (`exists_mulEquiv_of_comp_squareMap_eq`).

The isomorphic-split payload of Theorem (e) built from these
automorphisms — the invariant summands `F × 0` and `0 × F` swapped by a
`K`-equivariant isomorphism — is assembled downstream in this file's
follow-up sections.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki2Groups

open QuadraticExtension

noncomputable section

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (phi : RingAut F) (epsilon : F)

local instance instAlgebraZMod2TypeBSplit : Algebra (ZMod 2) F :=
  ZMod.algebra F 2

omit [Finite F] in
/-- **The type-B square map is `xφ(x)`-semilinear for the diagonal scalar
action**: `q(xa, xb) = xφ(x)·q(a, b)`. -/
theorem typeBQuadraticMap_smul (x : F) (v : F × F) :
    typeBQuadraticMap phi epsilon (x * v.1, x * v.2) =
      x * phi x * typeBQuadraticMap phi epsilon v := by
  simp only [typeBQuadraticMap_apply, map_mul]
  ring

/-- The diagonal scalar action of a unit on `F × F`, as an additive
automorphism. -/
def diagUnitsAddEquiv (x : Fˣ) : (F × F) ≃+ (F × F) :=
  AddEquiv.mk' (Equiv.prodCongr (Equiv.mulLeft₀ (x : F) x.ne_zero)
    (Equiv.mulLeft₀ (x : F) x.ne_zero)) (by
      intro v v'
      ext <;> simp [mul_add])

omit [Finite F] [CharP F 2] in
@[simp] theorem diagUnitsAddEquiv_apply (x : Fˣ) (v : F × F) :
    diagUnitsAddEquiv x v = ((x : F) * v.1, (x : F) * v.2) :=
  rfl

/-- The multiplication by `xφ(x)` on the central coordinate, as an
additive automorphism. -/
def normUnitsAddEquiv (x : Fˣ) : F ≃+ F :=
  AddEquiv.mk'
    (Equiv.mulLeft₀ ((x : F) * phi x)
      (mul_ne_zero x.ne_zero (Units.map (phi : F →* F) x).ne_zero))
    (mul_add ((x : F) * phi x))

omit [Finite F] [CharP F 2] in
@[simp] theorem normUnitsAddEquiv_apply (x : Fˣ) (w : F) :
    normUnitsAddEquiv phi x w = (x : F) * phi x * w :=
  rfl

/-- **The diagonal automorphisms of the type-B model** (Appendix III,
Theorem (e), p. 141): for each `x ∈ F*` the model `B(n, φ, ε)` has an
automorphism acting by `c ↦ xφ(x)·c` on the embedded center and by
`(a, b) ↦ (xa, xb)` on the quotient coordinate.  The compatible pair
`(diag x, xφ(x)·)` lifts by the Lemma 1(c) sufficiency. -/
theorem exists_diagonalAut (x : Fˣ) :
    ∃ Φ : MulAut (TypeBModel phi epsilon),
      (∀ w : F,
        Φ ((QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
            (Module.finBasis (ZMod 2) (F × F))).inl (Multiplicative.ofAdd w)) =
          (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
            (Module.finBasis (ZMod 2) (F × F))).inl
            (Multiplicative.ofAdd ((x : F) * phi x * w))) ∧
      ∀ e : TypeBModel phi epsilon,
        ((QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
            (Module.finBasis (ZMod 2) (F × F))).rightHom (Φ e)).toAdd =
          ((x : F) * ((QuadraticExtension.extension
              (typeBQuadraticMap phi epsilon)
              (Module.finBasis (ZMod 2) (F × F))).rightHom e).toAdd.1,
            (x : F) * ((QuadraticExtension.extension
              (typeBQuadraticMap phi epsilon)
              (Module.finBasis (ZMod 2) (F × F))).rightHom e).toAdd.2) := by
  obtain ⟨Φ, hinl, hright⟩ :=
    GroupExtension.exists_mulEquiv_of_comp_squareMap_eq
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F)))
      (QuadraticExtension.extension (typeBQuadraticMap phi epsilon)
        (Module.finBasis (ZMod 2) (F × F)))
      (range_inl_le_center _ _) (range_inl_le_center _ _)
      ⇑(typeBQuadraticMap phi epsilon) ⇑(typeBQuadraticMap phi epsilon)
      (Module.finBasis (ZMod 2) (F × F))
      (fun e => sq_eq_inl_q _ _ e) (fun e => sq_eq_inl_q _ _ e)
      (diagUnitsAddEquiv x) (normUnitsAddEquiv phi x)
      (fun v => by
        rw [normUnitsAddEquiv_apply, diagUnitsAddEquiv_apply]
        exact (typeBQuadraticMap_smul phi epsilon (x : F) v).symm)
  refine ⟨Φ, fun w => ?_, fun e => ?_⟩
  · rw [hinl w]
    rfl
  · rw [hright e]
    rfl

end

end OddOrder.Peterfalvi.Appendices.Suzuki2Groups
