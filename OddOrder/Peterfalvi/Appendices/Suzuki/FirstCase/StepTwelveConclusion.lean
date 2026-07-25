/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTwelveEndgame

/-!
# Peterfalvi Part II, Ch. II, step (12): conclusion

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (12), pp. 112–113 (conclusion).

The line-stabilizer analysis on `V = R₁/T` (three fixed lines force triviality),
the identification `N_G(R₁) = N_G(R)`, and the final transfer contradiction
with hypothesis (B2).
-/

set_option autoImplicit false

open scoped Pointwise commutatorElement

namespace OddOrder.Peterfalvi.Appendices.Suzuki

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)
  {F : Type uG} [NearFields.NearField F]
  (model : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
    NearFields.AffineNearFieldModel fc.rankOneQuotient F)

include model in
/-- **`[N_G(R), R] ≤ T`** ((12) tail, δ4-C1 — "the `R/T`-axis is centralized"):
writing `k = r₁·c` (`N_G(R) = R₁·C_G(P)`), the `c`-part moves only the
`T`-component of `r = t·y`, and the `r₁`-part contributes a commutator in
`⁅R₁,R₁⁆ = T`. -/
theorem conj_mul_inv_mem_sInvertedT_of_mem_invImageF
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3)
    (hR₁n : ∀ n ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G),
      ∀ x ∈ R₁, n * x * n⁻¹ ∈ R₁) {k r : G}
    (hk : k ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hr : r ∈ fc.invImageF model) :
    k * r * k⁻¹ * r⁻¹ ∈ fc.sInvertedT model := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  obtain ⟨hTle, -, -, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  -- decompose `k = r₁ · c`.
  obtain ⟨r₁, hr₁, c, hc, rfl⟩ := fc.exists_mul_eq_of_mem_normalizer model ind hB2
    hm hGp hSigma hRle hR₁le hcard hR₁n hk
  have hCle : Subgroup.centralizer (fc.P : Set G)
      ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
    have h1 := (fc.normalizer_P_lt_normalizer_invImageF model ind hm hGp hSigma).le
    rw [fc.normalizer_P_eq_centralizer] at h1
    exact h1
  -- the `c`-part: `c r c⁻¹ r⁻¹ ∈ T`.
  have hcT : c * r * c⁻¹ * r⁻¹ ∈ fc.sInvertedT model := by
    have hrTP : r ∈ (fc.sInvertedT model : Set G) * (fc.P : Set G) := by
      rw [← fc.coe_invImageF_eq_sInvertedT_mul_P model ind hB2 hm]
      exact hr
    obtain ⟨t, ht, y, hy, rfl⟩ := hrTP
    have hcy : c * y * c⁻¹ = y := by
      have h1 := Subgroup.mem_centralizer_iff.mp hc y hy
      rw [← h1]
      group
    have hct : c * t * c⁻¹ ∈ fc.sInvertedT model := by
      have h1 := fc.conj_sInvertedT_eq_of_mem_normalizer model ind hB2 hm hGp hSigma
        (hCle hc)
      have h2 := Subgroup.smul_mem_pointwise_smul t (MulAut.conj c)
        (fc.sInvertedT model) ht
      rwa [h1] at h2
    have hty : t * y = y * t :=
      fc.invImageF_mul_comm model ind hB2 hm t (hTle ht) y (fc.P_le_invImageF model hy)
    have hkey : c * (t * y) * c⁻¹ * (t * y)⁻¹ = (c * t * c⁻¹) * t⁻¹ := by
      calc c * (t * y) * c⁻¹ * (t * y)⁻¹
          = (c * t * c⁻¹) * ((c * y * c⁻¹) * (y⁻¹ * t⁻¹)) := by group
        _ = (c * t * c⁻¹) * (y * (y⁻¹ * t⁻¹)) := by rw [hcy]
        _ = (c * t * c⁻¹) * t⁻¹ := by group
    rw [hkey]
    exact mul_mem hct ((fc.sInvertedT model).inv_mem ht)
  -- the `r₁`-part contributes a commutator in `T`.
  have hw : c * r * c⁻¹ ∈ R₁ := by
    have h1 : c * r * c⁻¹ * r⁻¹ * r ∈ R₁ := mul_mem (hTle.trans hRle hcT) (hRle hr)
    have h2 : c * r * c⁻¹ * r⁻¹ * r = c * r * c⁻¹ := by group
    rwa [h2] at h1
  have hcomm : ⁅r₁, c * r * c⁻¹⁆ ∈ fc.sInvertedT model := by
    rw [← hcommT]
    exact Subgroup.commutator_mem_commutator hr₁ hw
  have hfinal : (r₁ * c) * r * (r₁ * c)⁻¹ * r⁻¹
      = ⁅r₁, c * r * c⁻¹⁆ * (c * r * c⁻¹ * r⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hfinal]
  exact mul_mem hcomm hcT

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
