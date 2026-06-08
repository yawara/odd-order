/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.CliffordAlgClosed
import OddOrder.GroupTheory.RepresentationTheory.SkolemNoether

/-!
# Multiplicity one: the restriction `V_H` is irreducible (BG Prop 2.2(a), the `m = 1` finish)

The final step of **Bender–Glauberman Proposition 2.2(a)**.  With `V_H` already known to be
`W`-isotypic (`isIsotypicOfType_of_conjugates`), this file shows the multiplicity is one, i.e.
`V_H` is itself irreducible, when `G = ⟨H, x⟩` (cyclic over `H`), `V` is `G`-irreducible, and the
field is algebraically closed.

The engine is Skolem–Noether (`SkolemNoether.lean`).  Conjugation by `ρ x` is an algebra
automorphism `θ` of `E = End_{k[H]} V` whose fixed subalgebra is `End_{k[G]} V = k` (Schur, `V`
irreducible over the algebraically closed `k`).  `E` is a simple algebra (isotypic), so
`finrank_eq_one_of_aut_fixedScalar` forces `finrank k E = 1`, whence `V_H` is simple.

## Main statements

* `cliffordConj` — conjugation by `ρ x`, as a `k`-algebra automorphism of `End_{k[H]} V`.
-/

namespace OddOrder.RepresentationTheory

open Representation
open scoped MonoidAlgebra

variable {G : Type*} [Group G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V]

section MultOne

variable (ρ : Representation k G V) (H : Subgroup G) [hH : H.Normal]

/-- Conjugating `H` by `x` then by `x⁻¹` is the identity. -/
theorem conjNormalMulAut_conjNormalMulAut_inv (x : G) (h : H) :
    conjNormalMulAut H x (conjNormalMulAut H x⁻¹ h) = h := by
  apply Subtype.ext
  simp only [conjNormalMulAut_apply_coe]
  group

/-- The induced ring automorphisms of `k[H]` for `x` and `x⁻¹` are mutually inverse. -/
theorem conjMonoidAlgRingHom_conj_inv (x : G) (r : k[↥H]) :
    conjMonoidAlgRingHom (k := k) (H := H) x (conjMonoidAlgRingHom (H := H) x⁻¹ r) = r := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single h c =>
      rw [conjMonoidAlgRingHom_single, conjMonoidAlgRingHom_single,
        conjNormalMulAut_conjNormalMulAut_inv]

variable {H}

/-- `ρ x⁻¹` followed by `ρ x` (as semilinear maps on the restriction) is the identity. -/
theorem conjSemilinearEnd_conj_inv (x : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ x (conjSemilinearEnd (H := H) ρ x⁻¹ v) = v := by
  rw [conjSemilinearEnd_apply, conjSemilinearEnd_apply]
  change (show (resRep ρ H).asModule from ρ x (ρ x⁻¹ v)) = v
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The `k[H]`-linear endomorphism `f ↦ ρ x ∘ f ∘ ρ x⁻¹` of the restriction.  It is `k[H]`-linear
(not merely `k`-linear) because the two conjugation twists cancel. -/
noncomputable def cliffordConjMap (x : G)
    (f : Module.End k[↥H] (resRep ρ H).asModule) :
    Module.End k[↥H] (resRep ρ H).asModule where
  toFun v := conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ v))
  map_add' v w := by simp only [map_add]
  map_smul' r v := by
    change conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ (r • v)))
      = r • conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ v))
    rw [LinearMap.map_smulₛₗ (conjSemilinearEnd (H := H) ρ x⁻¹), LinearMap.map_smul f,
      LinearMap.map_smulₛₗ (conjSemilinearEnd (H := H) ρ x), conjMonoidAlgRingHom_conj_inv]

@[simp] theorem cliffordConjMap_apply (x : G) (f : Module.End k[↥H] (resRep ρ H).asModule)
    (v : (resRep ρ H).asModule) :
    cliffordConjMap ρ x f v
      = conjSemilinearEnd (H := H) ρ x (f (conjSemilinearEnd (H := H) ρ x⁻¹ v)) :=
  rfl

/-- `ρ x` followed by `ρ x⁻¹` is the identity (the other cancellation). -/
theorem conjSemilinearEnd_inv_conj (x : G) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ x⁻¹ (conjSemilinearEnd (H := H) ρ x v) = v := by
  have := conjSemilinearEnd_conj_inv ρ x⁻¹ v
  rwa [inv_inv] at this

theorem cliffordConjMap_one (x : G) :
    cliffordConjMap ρ x (1 : Module.End k[↥H] (resRep ρ H).asModule) = 1 := by
  ext v
  simp only [cliffordConjMap_apply, Module.End.one_apply, conjSemilinearEnd_conj_inv]

theorem cliffordConjMap_mul (x : G) (f g : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConjMap ρ x (f * g) = cliffordConjMap ρ x f * cliffordConjMap ρ x g := by
  ext v
  simp only [cliffordConjMap_apply, Module.End.mul_apply, conjSemilinearEnd_inv_conj]

theorem cliffordConjMap_cliffordConjMap_inv (x : G)
    (f : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConjMap ρ x (cliffordConjMap ρ x⁻¹ f) = f := by
  ext v
  simp only [cliffordConjMap_apply, conjSemilinearEnd_inv_conj, conjSemilinearEnd_conj_inv]

/-- The induced ring automorphism of `k[H]` fixes the image of `k` (scalars). -/
theorem conjMonoidAlgRingHom_algebraMap (x : G) (c : k) :
    conjMonoidAlgRingHom (k := k) (H := H) x (algebraMap k k[↥H] c) = algebraMap k k[↥H] c := by
  have hc : (algebraMap k k[↥H] c) = MonoidAlgebra.single (1 : ↥H) c := by
    rw [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
  rw [hc, conjMonoidAlgRingHom_single, map_one]

/-- `conjSemilinearEnd ρ x` is `k`-linear (the conjugation twist fixes scalars). -/
theorem conjSemilinearEnd_smul_k (x : G) (c : k) (v : (resRep ρ H).asModule) :
    conjSemilinearEnd (H := H) ρ x (c • v) = c • conjSemilinearEnd (H := H) ρ x v := by
  rw [← algebraMap_smul k[↥H] c v, LinearMap.map_smulₛₗ, conjMonoidAlgRingHom_algebraMap,
    algebraMap_smul]

theorem cliffordConjMap_smul (x : G) (c : k)
    (f : Module.End k[↥H] (resRep ρ H).asModule) :
    cliffordConjMap ρ x (c • f) = c • cliffordConjMap ρ x f := by
  ext v
  simp only [cliffordConjMap_apply, LinearMap.smul_apply, conjSemilinearEnd_smul_k]

/-- **Conjugation by `ρ x`, as a `k`-algebra automorphism of `End_{k[H]} V`.**  The fixed
subalgebra is `End_{k[G]} V` (when `G = ⟨H, x⟩`); over an algebraically closed field with `V`
irreducible this is the scalars, which (via Skolem–Noether) forces multiplicity one. -/
noncomputable def cliffordConj (x : G) :
    Module.End k[↥H] (resRep ρ H).asModule ≃ₐ[k] Module.End k[↥H] (resRep ρ H).asModule where
  toFun := cliffordConjMap ρ x
  invFun := cliffordConjMap ρ x⁻¹
  left_inv f := by
    have := cliffordConjMap_cliffordConjMap_inv ρ x⁻¹ f
    rwa [inv_inv] at this
  right_inv f := cliffordConjMap_cliffordConjMap_inv ρ x f
  map_mul' := cliffordConjMap_mul ρ x
  map_add' f g := by ext v; simp only [cliffordConjMap_apply, LinearMap.add_apply, map_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, cliffordConjMap_smul, cliffordConjMap_one]

end MultOne

end OddOrder.RepresentationTheory
