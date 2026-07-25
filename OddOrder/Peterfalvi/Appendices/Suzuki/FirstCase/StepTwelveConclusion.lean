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

include model in
/-- **Fixing a third line forces membership in `R₁`** ((12) tail, δ4-C2): if
`k ∈ N_G(R)` fixes a line `X ∉ {R, T₁}` of `R₁/T`, then — since the `R/T`-axis is
centralized and the `T₁`-line is invariant — the conjugation defect of a mixed
generator lies in `X ⊓ T₁ = T`, so `k` centralizes all of `R₁/T` and lies in `R₁`. -/
theorem mem_of_conj_smul_eq_of_ne
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
      ∀ x ∈ R₁, n * x * n⁻¹ ∈ R₁) {X : Subgroup G}
    (hTX : fc.sInvertedT model ≤ X)
    (hXle : X ≤ R₁) (hXcard : Nat.card ↥X = fc.p ^ 2)
    (hXneR : X ≠ fc.invImageF model)
    (hXneT₁ : X ≠ fc.sInvertedOvergroup R₁) {k : G}
    (hk : k ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hfix : MulAut.conj k • X = X) :
    k ∈ R₁ := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  obtain ⟨hTle, hTinv, -, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hTcard : Nat.card ↥(fc.sInvertedT model) = fc.p := by
    rw [fc.card_sInvertedT model ind hB2 hm, hm, pow_one]
  have hcen := fc.sInvertedT_mul_comm_of_mem model ind hB2 hm hGp hSigma hR₁le hcard
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  obtain ⟨hT₁card, hTsubT₁, hT₁infP⟩ := fc.card_sInvertedOvergroup model ind hB2 hm
    hGp hSigma hRle hR₁le hcard hR₁n
  have hT₁le : fc.sInvertedOvergroup R₁ ≤ R₁ := fun x hx =>
    ((fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le
      hcard).mp hx).1
  have hRcard : Nat.card ↥(fc.invImageF model) = fc.p * fc.p := by
    rw [fc.card_invImageF model ind, hm, pow_one, fc.card_P]
  -- `R ⊔ X = R₁`.
  have hsup : fc.invImageF model ⊔ X = R₁ := by
    have hle : fc.invImageF model ⊔ X ≤ R₁ := sup_le hRle hXle
    have hdvd : Nat.card ↥(fc.invImageF model ⊔ X) ∣ fc.p ^ 3 := by
      have h1 := Subgroup.card_dvd_of_le hle
      rwa [hcard] at h1
    obtain ⟨i, hi3, hicard⟩ := (Nat.dvd_prime_pow fc.p_prime).mp hdvd
    have hge : fc.p ^ 2 ≤ Nat.card ↥(fc.invImageF model ⊔ X) := by
      have h1 := Subgroup.card_le_of_le
        (le_sup_right : X ≤ fc.invImageF model ⊔ X)
      rwa [hXcard] at h1
    have hne2 : Nat.card ↥(fc.invImageF model ⊔ X) ≠ fc.p ^ 2 := by
      intro h0
      have h1 : fc.invImageF model = fc.invImageF model ⊔ X := by
        apply Subgroup.eq_of_le_of_card_ge le_sup_left
        rw [h0, hRcard, pow_two]
      have h2 : X ≤ fc.invImageF model := by
        rw [h1]
        exact le_sup_right
      exact hXneR (Subgroup.eq_of_le_of_card_ge h2
        (by rw [hXcard, hRcard, pow_two]))
    have hi : i = 3 := by
      have h1 : fc.p ^ 2 ≤ fc.p ^ i := hicard ▸ hge
      have h2 : 2 ≤ i := by
        by_contra h3
        push Not at h3
        have h4 : fc.p ^ i < fc.p ^ 2 := Nat.pow_lt_pow_right fc.p_prime.one_lt h3
        omega
      rcases Nat.lt_or_ge i 3 with h | h
      · exfalso
        have h5 : i = 2 := by omega
        rw [h5] at hicard
        exact hne2 hicard
      · omega
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, hicard, hi]
  -- `X ⊓ T₁ = T`.
  have hXinfT₁ : X ⊓ fc.sInvertedOvergroup R₁ = fc.sInvertedT model := by
    have hTinf : fc.sInvertedT model ≤ X ⊓ fc.sInvertedOvergroup R₁ :=
      le_inf hTX hTsubT₁
    have hdvd : Nat.card ↥(X ⊓ fc.sInvertedOvergroup R₁) ∣ fc.p ^ 2 := by
      have h1 := Subgroup.card_dvd_of_le
        (inf_le_left : X ⊓ fc.sInvertedOvergroup R₁ ≤ X)
      rwa [hXcard] at h1
    obtain ⟨i, hi2, hicard⟩ := (Nat.dvd_prime_pow fc.p_prime).mp hdvd
    have hge : fc.p ≤ Nat.card ↥(X ⊓ fc.sInvertedOvergroup R₁) := by
      have h1 := Subgroup.card_le_of_le hTinf
      rwa [hTcard] at h1
    have hne2 : Nat.card ↥(X ⊓ fc.sInvertedOvergroup R₁) ≠ fc.p ^ 2 := by
      intro h0
      have h1 : X ⊓ fc.sInvertedOvergroup R₁ = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h0, hXcard])
      have h2 : X ≤ fc.sInvertedOvergroup R₁ := by
        rw [← h1]
        exact inf_le_right
      exact hXneT₁ (Subgroup.eq_of_le_of_card_ge h2 (by rw [hXcard, hT₁card]))
    have hi1 : i = 1 := by
      have h2 : 1 ≤ i := by
        by_contra h3
        push Not at h3
        have h4 : i = 0 := by omega
        rw [h4, pow_zero] at hicard
        rw [hicard] at hge
        have := fc.p_prime.one_lt
        omega
      rcases Nat.lt_or_ge i 2 with h | h
      · omega
      · exfalso
        have h5 : i = 2 := by omega
        rw [h5] at hicard
        exact hne2 hicard
    exact (Subgroup.eq_of_le_of_card_ge hTinf
      (by rw [hicard, hi1, hTcard, pow_one])).symm
  -- a mixed `T₁`-generator `t₁ = a·x'`.
  have hprod : ((fc.invImageF model ⊔ X : Subgroup G) : Set G)
      = (fc.invImageF model : Set G) * (X : Set G) := by
    refine Subgroup.coe_mul_of_right_le_normalizer_left _ _ ?_
    intro x hx
    exact hR₁le (hXle hx)
  obtain ⟨t₁, ht₁, ht₁T⟩ : ∃ t₁ ∈ fc.sInvertedOvergroup R₁,
      t₁ ∉ fc.sInvertedT model := by
    have h1 : ¬ fc.sInvertedOvergroup R₁ ≤ fc.sInvertedT model := by
      intro h
      have h2 := Subgroup.card_le_of_le h
      rw [hT₁card, hTcard] at h2
      have h3 := fc.p_prime.one_lt
      nlinarith
    obtain ⟨t₁, h1, h2⟩ := SetLike.not_le_iff_exists.mp h1
    exact ⟨t₁, h1, h2⟩
  have ht₁R₁ : t₁ ∈ ((fc.invImageF model ⊔ X : Subgroup G) : Set G) := by
    rw [hsup]
    exact hT₁le ht₁
  rw [hprod] at ht₁R₁
  obtain ⟨a, ha, x', hx', rfl⟩ := ht₁R₁
  have hx'nR : x' ∉ fc.invImageF model := by
    intro h0
    have h1 : a * x' ∈ fc.invImageF model ⊓ fc.sInvertedOvergroup R₁ :=
      ⟨mul_mem ha h0, ht₁⟩
    rw [fc.invImageF_inf_sInvertedOvergroup model ind hB2 hm hGp hSigma hRle hR₁le
      hcard] at h1
    exact ht₁T h1
  -- the defect of `x'` lies in `T`.
  have hδa : k * a * k⁻¹ * a⁻¹ ∈ fc.sInvertedT model :=
    fc.conj_mul_inv_mem_sInvertedT_of_mem_invImageF model ind hB2 hm hGp hSigma
      hRle hR₁le hcard hR₁n hk ha
  have hx'' : k * x' * k⁻¹ ∈ X := by
    have h1 := Subgroup.smul_mem_pointwise_smul x' (MulAut.conj k) X hx'
    rwa [hfix] at h1
  have hvX : (k * x' * k⁻¹) * x'⁻¹ ∈ X := mul_mem hx'' (inv_mem hx')
  have hc₄ : ⁅a, (k * x' * k⁻¹) * x'⁻¹⁆ ∈ fc.sInvertedT model := by
    rw [← hcommT]
    exact Subgroup.commutator_mem_commutator (hRle ha) (hXle hvX)
  have hwT₁ : k * (a * x') * k⁻¹ * (a * x')⁻¹ ∈ fc.sInvertedOvergroup R₁ := by
    have h1 := fc.conj_sInvertedOvergroup_eq model ind hB2 hm hGp hSigma hRle hR₁le
      hcard hR₁n hk
    have h2 := Subgroup.smul_mem_pointwise_smul (a * x') (MulAut.conj k)
      (fc.sInvertedOvergroup R₁) ht₁
    rw [h1] at h2
    exact mul_mem h2 ((fc.sInvertedOvergroup R₁).inv_mem ht₁)
  have hveq : (k * x' * k⁻¹) * x'⁻¹
      = ⁅a, (k * x' * k⁻¹) * x'⁻¹⁆⁻¹ * ((k * a * k⁻¹ * a⁻¹)⁻¹
        * (k * (a * x') * k⁻¹ * (a * x')⁻¹)) := by
    rw [commutatorElement_def]
    group
  have hδx' : (k * x' * k⁻¹) * x'⁻¹ ∈ fc.sInvertedT model := by
    rw [← hXinfT₁]
    refine ⟨hvX, ?_⟩
    rw [hveq]
    exact mul_mem (hTsubT₁ ((fc.sInvertedT model).inv_mem hc₄))
      (mul_mem (hTsubT₁ ((fc.sInvertedT model).inv_mem hδa)) hwT₁)
  -- the defect subgroup contains `R` and `x'`, hence all of `R₁`.
  set S₂ : Set G := {x : G | x ∈ R₁ ∧
    k * x * k⁻¹ * x⁻¹ ∈ fc.sInvertedT model} with hS₂def
  have hsub : ∃ H : Subgroup G, (H : Set G) = S₂ := by
    refine ⟨⟨⟨⟨S₂, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · rintro a' b' ⟨haR, hai⟩ ⟨hbR, hbi⟩
      refine ⟨mul_mem haR hbR, ?_⟩
      have hswap := hcen _ hbi a' haR
      have h1 : a' * (k * b' * k⁻¹ * b'⁻¹) * a'⁻¹ = k * b' * k⁻¹ * b'⁻¹ := by
        rw [hswap]
        group
      have hkey : k * (a' * b') * k⁻¹ * (a' * b')⁻¹
          = (k * a' * k⁻¹ * a'⁻¹) * (a' * (k * b' * k⁻¹ * b'⁻¹) * a'⁻¹) := by
        group
      rw [hkey, h1]
      exact mul_mem hai hbi
    · refine ⟨one_mem _, ?_⟩
      have h1 : k * 1 * k⁻¹ * 1⁻¹ = 1 := by group
      rw [h1]
      exact one_mem _
    · rintro a' ⟨haR, hai⟩
      refine ⟨inv_mem haR, ?_⟩
      have hswap := hcen _ ((fc.sInvertedT model).inv_mem hai) a'⁻¹ (inv_mem haR)
      have h1 : k * a'⁻¹ * k⁻¹ * a'⁻¹⁻¹
          = a'⁻¹ * (k * a' * k⁻¹ * a'⁻¹)⁻¹ * a' := by
        group
      have h2 : a'⁻¹ * (k * a' * k⁻¹ * a'⁻¹)⁻¹ * a'
          = (k * a' * k⁻¹ * a'⁻¹)⁻¹ := by
        rw [hswap]
        group
      rw [h1, h2]
      exact (fc.sInvertedT model).inv_mem hai
  obtain ⟨D₀, hD₀⟩ := hsub
  have hD₀mem : ∀ x : G, x ∈ D₀ ↔ (x ∈ R₁ ∧
      k * x * k⁻¹ * x⁻¹ ∈ fc.sInvertedT model) := by
    intro x
    rw [← SetLike.mem_coe, hD₀]
    exact Iff.rfl
  have hRD : fc.invImageF model ≤ D₀ := by
    intro r hr
    rw [hD₀mem]
    exact ⟨hRle hr, fc.conj_mul_inv_mem_sInvertedT_of_mem_invImageF model ind hB2
      hm hGp hSigma hRle hR₁le hcard hR₁n hk hr⟩
  have hx'D : x' ∈ D₀ := by
    rw [hD₀mem]
    exact ⟨hXle hx', hδx'⟩
  have hD₀le : D₀ ≤ R₁ := fun x hx => ((hD₀mem x).mp hx).1
  have hD₀eq : D₀ = R₁ := by
    have hdvd : Nat.card ↥D₀ ∣ fc.p ^ 3 := by
      have h1 := Subgroup.card_dvd_of_le hD₀le
      rwa [hcard] at h1
    obtain ⟨i, hi3, hicard⟩ := (Nat.dvd_prime_pow fc.p_prime).mp hdvd
    have hge : fc.p ^ 2 ≤ Nat.card ↥D₀ := by
      have h1 := Subgroup.card_le_of_le hRD
      rwa [hRcard, ← pow_two] at h1
    have hne2 : Nat.card ↥D₀ ≠ fc.p ^ 2 := by
      intro h0
      have h1 : fc.invImageF model = D₀ :=
        Subgroup.eq_of_le_of_card_ge hRD (by rw [h0, hRcard, pow_two])
      rw [← h1] at hx'D
      exact hx'nR hx'D
    have hi : i = 3 := by
      have h1 : fc.p ^ 2 ≤ fc.p ^ i := hicard ▸ hge
      have h2 : 2 ≤ i := by
        by_contra h3
        push Not at h3
        have h4 : fc.p ^ i < fc.p ^ 2 := Nat.pow_lt_pow_right fc.p_prime.one_lt h3
        omega
      rcases Nat.lt_or_ge i 3 with h | h
      · exfalso
        have h5 : i = 2 := by omega
        rw [h5] at hicard
        exact hne2 hicard
      · omega
    apply Subgroup.eq_of_le_of_card_ge hD₀le
    rw [hcard, hicard, hi]
  have hall : ∀ x ∈ R₁, k * x * k⁻¹ * x⁻¹ ∈ fc.sInvertedT model := by
    intro x hx
    rw [← hD₀eq] at hx
    exact ((hD₀mem x).mp hx).2
  exact fc.mem_of_forall_conj_mul_inv_mem_sInvertedT model ind hB2 hm hGp hSigma
    hRle hR₁le hcard hk hall

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
