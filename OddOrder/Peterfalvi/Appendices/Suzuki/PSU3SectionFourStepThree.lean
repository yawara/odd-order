/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3SectionFourIntrinsic

/-!
# Ch. IV §4, steps (2) and (3) on `U/Z(U)` and back in `G`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §4, p. 133.

Step (2) runs §2 and §3 "relative to `U`"; `PSU3SectionFourCorollaryTwo` proves
Corollary 2 there for the *transported* standing hypothesis, and
`PSU3SectionFourIntrinsic` matches that hypothesis with the *intrinsic* one, whose
mappings are the book's `f₁`, `h₁`.  This file states step (2) for the intrinsic
hypothesis and then reads its conclusion back into `G`, which is step (3).

## Main results

* `Hypothesis.corollaryTwo_intrinsicResidualQuotient` — step (2) for the intrinsic
  standing hypothesis on `U/Z(U)`.
* `Hypothesis.exists_f_eq_conj_inv_residual` — step (3): `f(ω) = ω^{-ζ}` in `G`.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace Hypothesis

open OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
open scoped Pointwise

universe u v

variable {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {X : Subgroup G}
  [MulAction (hyp.centralizerActionQuotient X) ↥(MulAction.fixedPoints X Ω)]
  {result : TheoremAConclusion (hyp.centralizerActionQuotient X)
    ↥(MulAction.fixedPoints X Ω)}
  {data : PSU3InductionTarget (Omega := ↥(MulAction.fixedPoints X Ω)) result.L}

/-- **🎯 Ch. IV §4, step (2) for the *intrinsic* standing hypothesis on `U/Z(U)`**
(Peterfalvi Part II, p. 133).

`corollaryTwo_residualQuotient` proves Corollary 2 on the transported hypothesis; the
book's `f₁`, `h₁` are the mappings of the intrinsic one, whose `H`, `Q`, `D`, `t` are the
images of `U ∩ H`, `U ∩ Q`, `U ∩ D` and `t`.  The two are matched by
`exists_mulEquiv_match_residualQuotient_t`, and `corollaryTwo_conclusion_of_mulEquiv`
(through `IsFGH.map`) pushes the witness across. -/
theorem corollaryTwo_intrinsicResidualQuotient (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∀ ζ ∈ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W, ζ ≠ 1 →
      ∃ f₂ g₂ k₂ : (↥(residualImage (G := G) X) ⧸
            Subgroup.center ↥(residualImage (G := G) X)) →
          ↥(residualImage (G := G) X) ⧸ Subgroup.center ↥(residualImage (G := G) X),
        OddOrder.GroupTheory.RankOneBNPair.IsFGH
            (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).H
            (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q
            (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).D
            (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).t f₂ g₂ k₂ ∧
          ∃ ω ∈ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q,
            ω ∉ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).Q0 ∧
              f₂ ω = ζ⁻¹ * ω⁻¹ * ζ ∧ k₂ ω = ζ ^ 3 := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  intro ζ hζW hζ1
  obtain ⟨ψ, hH, hQ, hD, ht⟩ :=
    hyp.exists_mulEquiv_match_residualQuotient_t details hXD htX hCQ hZD
  -- pull `ζ` back along `ψ`
  have hWmap := map_W_of_mulEquiv (hyp.residualQuotientHypothesis details)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) ψ hH hD
  obtain ⟨ζ₀, hζ₀W, hζ₀ζ⟩ : ∃ ζ₀ ∈ (hyp.residualQuotientHypothesis details).W, ψ ζ₀ = ζ := by
    rw [← hWmap] at hζW
    exact hζW
  have hζ₀1 : ζ₀ ≠ 1 := by
    intro hc
    exact hζ1 (by rw [← hζ₀ζ, hc, map_one])
  obtain ⟨f₁, g₁, k₁, H₁, ω, hωQ, hωQ0, hf, hk⟩ :=
    hyp.corollaryTwo_residualQuotient details hXV hX ih ζ₀ hζ₀W hζ₀1
  obtain ⟨f₂, g₂, k₂, H₂, -⟩ :=
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).exists_fgh_mapsTo
  obtain ⟨h1, h2, h3, h4⟩ := corollaryTwo_conclusion_of_mulEquiv
    (hyp.residualQuotientHypothesis details)
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD) ψ hH hQ hD ht H₁ H₂ hωQ hωQ0
    hf hk
  rw [hζ₀ζ] at h3 h4
  exact ⟨f₂, g₂, k₂, H₂, ψ ω, h1, h2, h3, h4⟩


/-- **🎯 Ch. IV §4, step (3): `f(ω) = ω^{-ζ}` in `G`** (Peterfalvi Part II, p. 133).

Step (2) computes on `U/Z(U)`; this reads the answer back into `G`:

* the witness `ω̄` and the parameter `ζ̄` lift to `U` (`Q̄` and `D̄` are images);
* `fgh_residualQuotient_eq` turns step (2)'s equation into one between the images of the
  `U`-relative mappings;
* `eq_of_mk_eq_of_mem_Q` upgrades it to an equation in `U` — both sides lie in `Q ∩ U`,
  where the projection is injective;
* `exists_fgh_residual` — the uniqueness of the canonical form — replaces the
  `U`-relative `f₁` by the ambient `f`.

`ζ` comes out in `D ∩ U` rather than in `W`: `W̄ ≤ D̄` is what lifts, an element of `U`
centralizing `Q₀ ∩ U` need not centralize `Q₀`.  The book's sharper `ζ ∈ C_W(P ∩ U)` is a
refinement of the same element. -/
theorem exists_f_eq_conj_inv_residual {f g h : G → G}
    (Hfgh : OddOrder.GroupTheory.RankOneBNPair.IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hXV : X ≤ hyp.V) (hX : X ≠ ⊥)
    (details : CentralizerPSUData hyp X result data)
    (hXD : X ≤ hyp.D) (htX : hyp.t ∈ Subgroup.centralizer (X : Set G))
    (hCQ : IsPGroup 2 ↥(hyp.Q.subgroupOf (Subgroup.centralizer (X : Set G))))
    (hZD : Subgroup.center ↥(residualImage (G := G) X)
      ≤ hyp.D.subgroupOf (residualImage (G := G) X))
    (ih : TheoremAInductionBelow G Ω) :
    letI := MulAction.compHom (ULift.{v} (Unital data.n))
      details.residualQuotientEquiv.toMonoidHom
    ∀ ζ ∈ (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W, ζ ≠ 1 →
      ∃ z x : ↥(residualImage (G := G) X), (z : G) ∈ hyp.D ∧ (x : G) ∈ hyp.Q ∧
        (x : G) ∉ hyp.Q0 ∧
        f (x : G) = (z : G)⁻¹ * (x : G)⁻¹ * (z : G) := by
  letI := MulAction.compHom (ULift.{v} (Unital data.n))
    details.residualQuotientEquiv.toMonoidHom
  intro ζ hζW hζ1
  obtain ⟨f₂, g₂, k₂, H₂, ω, hωQ, hωQ0, hfω, -⟩ :=
    hyp.corollaryTwo_intrinsicResidualQuotient hXV hX details hXD htX hCQ hZD ih ζ hζW hζ1
  obtain ⟨f₁, g₁, h₁, H₁, hamb⟩ := hyp.exists_fgh_residual Hfgh hXD htX hCQ
  obtain ⟨x, hxQ, hxω⟩ := hωQ
  obtain ⟨z, hzD, hzζ⟩ :
      ζ ∈ (hyp.D.subgroupOf (residualImage (G := G) X)).map
        (QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))) :=
    (hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).V_le_D
      ((hyp.intrinsicResidualQuotient details hXD htX hCQ hZD).W_le_V hζW)
  have hxQ' : (x : G) ∈ hyp.Q := Subgroup.mem_subgroupOf.mp hxQ
  have hzD' : (z : G) ∈ hyp.D := Subgroup.mem_subgroupOf.mp hzD
  -- `x ∉ Q₀`, since its image is not in `Q̄₀`
  have hxQ0 : (x : G) ∉ hyp.Q0 := by
    intro hc
    refine hωQ0 ?_
    rw [← hxω, Hypothesis.mem_Q0_iff]
    refine ⟨?_, ?_⟩
    · have hsq : (x : ↥(residualImage (G := G) X)) ^ 2 = 1 := by
        refine Subtype.ext ?_
        push_cast
        exact hc.1
      rw [← map_pow, hsq, map_one]
    · exact ⟨x, (hyp.rankOneSetup_residual hXD htX hCQ).QM hxQ, rfl⟩
  have hx1 : QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) x ≠ 1 := by
    rw [hxω]
    intro hc
    exact hωQ0 (by rw [hc]; exact (hyp.intrinsicResidualQuotient details hXD htX hCQ
      hZD).Q0.one_mem)
  have hxU1 : x ≠ 1 := fun hc => hx1 (by rw [hc, map_one])
  have hxne : (x : G) ≠ 1 := fun hc => hxU1 (Subtype.ext hc)
  -- the equation between the images
  obtain ⟨hf₂, -⟩ := hyp.fgh_residualQuotient_eq hXD htX hCQ hZD H₁ H₂ hxQ' hx1
  have hmk : QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X)) (f₁ x)
      = QuotientGroup.mk' (Subgroup.center ↥(residualImage (G := G) X))
        (z⁻¹ * x⁻¹ * z) := by
    rw [← hf₂, hxω, hfω, ← hzζ, ← hxω]
    simp only [map_mul, map_inv]
  obtain ⟨hfQ₁, -, -⟩ := H₁.mem x hxQ hxU1
  have hconj : z⁻¹ * x⁻¹ * z ∈ hyp.Q.subgroupOf (residualImage (G := G) X) :=
    (hyp.rankOneSetup_residual hXD htX hCQ).DQ z hzD x⁻¹ (Subgroup.inv_mem _ hxQ)
  have heq : f₁ x = z⁻¹ * x⁻¹ * z :=
    hyp.eq_of_mk_eq_of_mem_Q hXD htX hCQ hZD (Subgroup.mem_subgroupOf.mp hfQ₁)
      (Subgroup.mem_subgroupOf.mp hconj) hmk
  refine ⟨z, x, hzD', hxQ', hxQ0, ?_⟩
  rw [← (hamb x hxQ' hxne).1, heq]
  push_cast
  rfl

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
