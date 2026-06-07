/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.EigenspaceBlockDecomp
import OddOrder.GroupTheory.RepresentationTheory.CyclicEndConjCount

/-!
# Towards Bender–Glauberman Theorem 2.5 (the divisibility conclusion)

`OddOrder.GroupTheory.RepresentationTheory` shared module assembling the BG §2 Prop 2.4 machinery
into the **divisibility step** of Theorem 2.5: for a faithful representation `V` of `P ⋊ ⟨x⟩` with
`P` extraspecial and `x` acting on `End_F V` by conjugation, `h ∣ qⁿ ± 1` where `q = dim V`.

This file does the *consumer-side* wiring, reducing the conclusion to the single remaining input
**`dim E₀ = dim E_m + 1`** (the `E(P) = principal ⊕ regular` H-module structure of BG (2.11),
which comes from `C_{P/Z}(x) = 1`). Given that input, Prop 2.4(h)
(`sum_sq_sub_finrank_cyclicEndConjEigenspaceFin`) turns it into `∑ᵢ(nᵢ−nᵢ₊ₘ)² = 2`, and
`prop24j_fin` concludes `q = h·v₀ + δ` with `δ = ±1`.
-/

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **BG Theorem 2.5, divisibility step (conditional on the H-module multiplicities).** If the
conjugation eigenspaces satisfy `dim E₀ = dim E_m + 1` for all `m ≠ 0` (the `principal ⊕ regular`
structure), then `q := ∑ᵢ dim Vᵢ = dim V` satisfies `q = h·v₀ + δ` with `δ = ±1`, i.e.
`q ≡ ±1 (mod h)`. -/
theorem sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} [NeZero h] [FiniteDimensional F V]
    (hprim : IsPrimitiveRoot epsilon h)
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon (g : Module.End F V) h))
    (hh : 2 ≤ h)
    (hEdim : ∀ m : Fin h, m ≠ 0 →
      finrank F (cyclicEndConjEigenspaceFin epsilon g (0 : Fin h))
        = finrank F (cyclicEndConjEigenspaceFin epsilon g m) + 1) :
    ∃ (v₀ δ : ℤ), (δ = 1 ∨ δ = -1) ∧
      (∑ i : Fin h, (cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ))
        = (h : ℤ) * v₀ + δ := by
  have Hsum : ∀ m : Fin h, m ≠ 0 →
      ∑ i : Fin h, ((cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ)
        - (cyclicEigenspaceFinDim epsilon (g : Module.End F V) (i + m) : ℤ)) ^ 2 = 2 := by
    intro m hm
    rw [sum_sq_sub_finrank_cyclicEndConjEigenspaceFin hprim hV m, hEdim m hm]
    push_cast; ring
  obtain ⟨_, v₀, δ, hδ, _, _, hsum⟩ :=
    prop24j_fin hh (fun i => (cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ)) Hsum
  exact ⟨v₀, δ, hδ, hsum⟩

end OddOrder.RepresentationTheory
