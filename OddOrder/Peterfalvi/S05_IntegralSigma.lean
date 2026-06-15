/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_SigmaIsometry
import OddOrder.Peterfalvi.S07_Coherence

/-!
# Peterfalvi §5: the (3.2) σ-isometry as an integral character map

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§3 (repo chunk 04.3), result (3.2).

This is a **signature-bridge leaf** for the FT critical path
(`notes/meta/ft_path_policy.md` §4, endpoint **C**).  It exposes the ℂ-linear
(3.2) σ-isometry `S05.TICyclicHypothesis.sigma`
(`ClassFunction ↥W ℂ →ₗ[ℂ] ClassFunction G ℂ`) as an *integral* character map
`S07.IntegralCharacterMap ↥W G` (`ClassFunction ↥W ℂ →ₗ[ℤ] ClassFunction G ℂ`),
which is the exact type that the §13 `S,T`-grid hypothesis field
`S15.Hypothesis.tau3` is pinned to (`η_{ij} = ω_{ij}^{τ₃}`, Peterfalvi (13.1.d)).

A ℂ-linear map is automatically ℤ-linear, so the bridge is
`LinearMap.restrictScalars ℤ`; every property carries over verbatim from the
σ-isometry.  Pinning the consumer side (`S15.Hypothesis.tau3 := …`) is the
§13-spine owner's wiring step; here we only supply the citeable endpoint.

Depends only on the `TICyclicHypothesis` for `W` (pure §5 character theory) — it
is **not** gated on the §10–16 maximal-subgroup structure.
-/

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

namespace TICyclicHypothesis

variable (hyp : TICyclicHypothesis G) [Fintype hyp.W]
  [Invertible (Nat.card hyp.W : ℂ)] [Invertible (Nat.card G : ℂ)]
  (hVeq : hyp.V = hyp.Vdiff) (app : FullDadeApplication (G := G) hyp)

/-- **Peterfalvi (3.2), integral form.**  The ℂ-linear σ-isometry
(`TICyclicHypothesis.sigma`) re-viewed as an integral (ℤ-linear) character map
on the virtual-character lattice.  This is the concrete
`S07.IntegralCharacterMap ↥W G` that `S15.Hypothesis.tau3` is pinned to. -/
noncomputable def sigmaIntegral :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap hyp.W G :=
  (hyp.sigma hVeq app).restrictScalars ℤ

@[simp] theorem sigmaIntegral_apply (φ : ClassFunction hyp.W ℂ) :
    hyp.sigmaIntegral hVeq app φ = hyp.sigma hVeq app φ :=
  rfl

/-- The integral (3.2) map is an integral isometry (Peterfalvi (3.2), isometry
part). -/
theorem sigmaIntegral_isIntegralIsometry :
    OddOrder.Peterfalvi.S07.IsIntegralIsometry (hyp.sigmaIntegral hVeq app) :=
  ⟨fun φ ψ => hyp.sigma_inner hVeq app φ ψ⟩

/-- The integral (3.2) map sends the trivial character of `W` to that of `G`. -/
theorem sigmaIntegral_trivial :
    hyp.sigmaIntegral hVeq app (trivialClassFunction hyp.W) = trivialClassFunction G :=
  hyp.sigma_trivial hVeq app

/-- The integral (3.2) map sends virtual characters to virtual characters. -/
theorem sigmaIntegral_mem_ZIrr {z : ClassFunction hyp.W ℂ} (hz : z ∈ ZIrr hyp.W) :
    hyp.sigmaIntegral hVeq app z ∈ ZIrr G :=
  hyp.sigma_mem_ZIrr hVeq app hz

/-- **Peterfalvi (3.2)(c)** for the integral map: it is the identity on `V`. -/
theorem sigmaIntegral_apply_of_mem_V (α : ClassFunction hyp.W ℂ) {v : G}
    (hv : v ∈ hyp.V) :
    hyp.sigmaIntegral hVeq app α v = α ⟨v, hyp.V_subset_W hv⟩ :=
  hyp.sigma_apply_of_mem_V hVeq app α hv

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05
