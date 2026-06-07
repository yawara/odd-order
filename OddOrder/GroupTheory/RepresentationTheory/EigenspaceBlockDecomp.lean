/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceUnderCyclicAction

/-!
# Block decomposition of `End V` (BG Prop 2.4(c)/(g))

`OddOrder.GroupTheory.RepresentationTheory` shared module towards the `(g)` step of
**Bender–Glauberman Proposition 2.4**: `dim E_m = ∑ᵢ nᵢ nᵢ₊ₘ` for the conjugation
eigenspaces `E_m`, via the block decomposition `End V = ⊕_{i,t} Hom(Vᵢ, Vₜ)`.

First building block: the reconstruction `∑ᵢ (component i of v) = v` for the internal
eigenspace decomposition `V = ⊕ᵢ Vᵢ` of Prop 2.4(a).
-/

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **Reconstruction of a vector from its eigenspace components.** -/
theorem sum_cyclicEigenspaceFinDecomposition_eq {epsilon : F} {g : Module.End F V} {h : ℕ}
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon g h)) (v : V) :
    ∑ i, ((cyclicEigenspaceFinDecomposition hV v i :
      cyclicEigenspaceFinFamily epsilon g h i) : V) = v := by
  classical
  have hcoe : DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h)
      (cyclicEigenspaceFinDecomposition hV v) = v :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily epsilon g h))
      hV).apply_symm_apply v
  conv_rhs => rw [← hcoe, DirectSum.coeLinearMap_eq_dfinsuppSum]
  rw [DFinsupp.sum_eq_sum_fintype _ (fun _ => rfl)]
  simp

end OddOrder.RepresentationTheory
