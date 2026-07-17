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

/-- **The `W₂`-component lift** of a character of `W`: `χ ↦ (χ|_{W₂}) ∘ wSnd` — the character
`ω_{0j}` sharing `χ`'s `W₂`-component but trivial on `W₁` (the `w_ 0 j` of the Coq `ew`-basis). -/
noncomputable def sndPart (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) : hyp.W →* ℂˣ :=
  (χ.comp (hyp.W2.subgroupOf hyp.W).subtype).comp hyp.wSnd

/-- On `W₂` the lift agrees with `χ` (`wSnd` is the identity there). -/
theorem sndPart_apply_of_mem_W2 (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W2.subgroupOf hyp.W) :
    hyp.sndPart χ w = χ w := by
  have hsymm : hyp.wProdEquiv.symm w = (1, ⟨w, hw⟩) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  simp [sndPart, wSnd_apply, hsymm]

/-- The lift only sees the `W₂`-component: `sndPart χ w = sndPart χ (ι₂ (wSnd w))`. -/
theorem sndPart_apply_eq_apply_sndProj (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ)
    (w : hyp.W) :
    hyp.sndPart χ ((hyp.W2.subgroupOf hyp.W).subtype (hyp.wSnd w)) = hyp.sndPart χ w := by
  have hmem : ((hyp.W2.subgroupOf hyp.W).subtype (hyp.wSnd w)) ∈ hyp.W2.subgroupOf hyp.W :=
    (hyp.wSnd w).2
  rw [sndPart_apply_of_mem_W2 hyp χ hmem]
  rfl

open scoped Classical in
/-- **The `ω`-difference family spans `CF(W, W ∖ W₂)`** (the Coq `V2basis` step of
`primeTIirr_spec`, spanning half): every class function of `W` vanishing on `W₂` lies in the
span of the differences `ω_χ − ω_{sndPart χ}`.

Proof: Fourier-expand `f = Σ_χ c_χ • ω_χ` and split off
`g := Σ_χ c_χ • ω_{sndPart χ}`.  Then `g = f − Σ c_χ•(ω_χ − ω_{sndPart χ})` vanishes on `W₂`
(each difference does, and `f` does), while every value `g(w)` equals `g` at the
`W₂`-component of `w` (`sndPart_apply_eq_apply_sndProj`) — a point of `W₂` — so `g = 0`
identically, leaving `f` in the span of the differences. -/
theorem supported_le_span_omega_sub_sndPart (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] [Fintype (hyp.W →* ℂˣ)] :
    ClassFunction.supportedSubmodule {w : hyp.W | w ∉ hyp.W2.subgroupOf hyp.W} ≤
      Submodule.span ℂ (Set.range (fun χ : hyp.W →* ℂˣ =>
        (hyp.omega χ : ClassFunction hyp.W ℂ) - hyp.omega (hyp.sndPart χ))) := by
  intro f hf
  have hf0 : ∀ w : hyp.W, w ∈ hyp.W2.subgroupOf hyp.W → f w = 0 := by
    intro w hw
    by_contra h0
    exact (ClassFunction.mem_supportedSubmodule.mp hf
      (ClassFunction.mem_support.mpr h0)) hw
  -- Fourier expansion and the split.
  have hexp := hyp.eq_sum_inner_smul_omega f
  set c : (hyp.W →* ℂˣ) → ℂ := fun χ => ClassFunction.inner f (hyp.omega χ) with hc
  set g : ClassFunction hyp.W ℂ :=
    ∑ χ : hyp.W →* ℂˣ, c χ • (hyp.omega (hyp.sndPart χ) : ClassFunction hyp.W ℂ) with hg
  have hsplit : f = (∑ χ : hyp.W →* ℂˣ,
      c χ • ((hyp.omega χ : ClassFunction hyp.W ℂ) - hyp.omega (hyp.sndPart χ))) + g := by
    rw [hg]
    rw [← Finset.sum_add_distrib]
    rw [hexp]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [smul_sub]
    abel
  -- `g` vanishes on `W₂` …
  have hgW2 : ∀ w : hyp.W, w ∈ hyp.W2.subgroupOf hyp.W → g w = 0 := by
    intro w hw
    have hfw : f w = 0 := hf0 w hw
    have hdiff : ∀ χ : hyp.W →* ℂˣ,
        (c χ • ((hyp.omega χ : ClassFunction hyp.W ℂ) - hyp.omega (hyp.sndPart χ))) w = 0 := by
      intro χ
      have hval : (hyp.omega χ : ClassFunction hyp.W ℂ) w
          = (hyp.omega (hyp.sndPart χ) : ClassFunction hyp.W ℂ) w := by
        rw [omega_apply, omega_apply, sndPart_apply_of_mem_W2 hyp χ hw]
      change c χ * ((hyp.omega χ : ClassFunction hyp.W ℂ) w
        - (hyp.omega (hyp.sndPart χ) : ClassFunction hyp.W ℂ) w) = 0
      rw [hval, sub_self, mul_zero]
    have hsum0 : (∑ χ : hyp.W →* ℂˣ,
        c χ • ((hyp.omega χ : ClassFunction hyp.W ℂ) - hyp.omega (hyp.sndPart χ))) w = 0 := by
      rw [ClassFunction.finset_sum_apply]
      exact Finset.sum_eq_zero fun χ _ => hdiff χ
    have happly := congrArg (fun φ : ClassFunction hyp.W ℂ => φ w) hsplit
    change f w = (∑ χ : hyp.W →* ℂˣ,
        c χ • ((hyp.omega χ : ClassFunction hyp.W ℂ) - hyp.omega (hyp.sndPart χ))) w
      + g w at happly
    rw [hfw, hsum0, zero_add] at happly
    exact happly.symm
  -- … and `g` only sees the `W₂`-component, so `g = 0`.
  have hg0 : g = 0 := by
    ext w
    have hproj : g w = g ((hyp.W2.subgroupOf hyp.W).subtype (hyp.wSnd w)) := by
      rw [hg, ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply]
      refine Finset.sum_congr rfl fun χ _ => ?_
      change c χ * (hyp.omega (hyp.sndPart χ) : ClassFunction hyp.W ℂ) w
        = c χ * (hyp.omega (hyp.sndPart χ) : ClassFunction hyp.W ℂ) _
      rw [omega_apply, omega_apply, sndPart_apply_eq_apply_sndProj hyp χ w]
    rw [hproj,
      hgW2 ((hyp.W2.subgroupOf hyp.W).subtype (hyp.wSnd w)) (hyp.wSnd w).2]
    rfl
  rw [hsplit, hg0, add_zero]
  exact Submodule.sum_mem _ fun χ _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)

end OddOrder.Peterfalvi.S05.TICyclicHypothesis
