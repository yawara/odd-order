/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_TICyclic
import OddOrder.GroupTheory.RepresentationTheory.SupportedSpanOrthogonality

/-!
# The `ω`-grid spans `CF(W)` — Fourier expansion over the cyclic-TI grid

For the cyclic `W` of a `TICyclicHypothesis`, the linear characters `ω_χ` (`χ : W →* ℂˣ`)
exhaust `Irr(W)` (`omega_surjective`), so they span all class functions
(`span_irreducibleCharacter_eq_top`) and every `f ∈ CF(W)` has the Fourier expansion
`f = Σ_χ ⟨f, ω_χ⟩ • ω_χ` (the orthonormal-spanning expansion of `SupportedSpanOrthogonality`).

This is the base layer of the Coq `V2basis` step of `primeTIirr_spec` (`PFsection4.v:340`):
the `ω`-difference family spanning `CF(W, W ∖ W₂)`, toward the prime-TI value identity
(4.3.c)/`prTIirr_id` and the Peterfalvi (13.18)/(13.19) grid facts (issue 2038 chain).
-/

namespace OddOrder.Peterfalvi.S05.TICyclicHypothesis

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- **The `ω`-family spans `CF(W)`** (`Irr(W) = {ω_χ}` + character completeness). -/
theorem span_omega_eq_top (hyp : TICyclicHypothesis G) :
    Submodule.span ℂ (Set.range (fun χ : hyp.W →* ℂˣ =>
      (hyp.omega χ : ClassFunction hyp.W ℂ))) = ⊤ := by
  have hrange : Set.range (fun χ : hyp.W →* ℂˣ => (hyp.omega χ : ClassFunction hyp.W ℂ))
      = Set.range (fun φ : IrreducibleCharacter hyp.W => (φ : ClassFunction hyp.W ℂ)) := by
    ext f
    constructor
    · rintro ⟨χ, rfl⟩
      exact ⟨hyp.omega χ, rfl⟩
    · rintro ⟨φ, rfl⟩
      obtain ⟨χ, rfl⟩ := hyp.omega_surjective φ
      exact ⟨χ, rfl⟩
  rw [hrange]
  exact span_irreducibleCharacter_eq_top

open scoped Classical in
/-- **Fourier expansion over the `ω`-grid**: every class function of the cyclic `W` is
`f = Σ_χ ⟨f, ω_χ⟩ • ω_χ`. -/
theorem eq_sum_inner_smul_omega (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Fintype (hyp.W →* ℂˣ)] (f : ClassFunction hyp.W ℂ) :
    f = ∑ χ : hyp.W →* ℂˣ,
      ClassFunction.inner f (hyp.omega χ) • (hyp.omega χ : ClassFunction hyp.W ℂ) := by
  exact eq_sum_inner_smul_of_orthonormal_of_span_top
    (fun χ : hyp.W →* ℂˣ => (hyp.omega χ : ClassFunction hyp.W ℂ))
    (fun χ χ' => hyp.omega_inner χ χ')
    (le_of_eq (span_omega_eq_top hyp).symm) f

end OddOrder.Peterfalvi.S05.TICyclicHypothesis
