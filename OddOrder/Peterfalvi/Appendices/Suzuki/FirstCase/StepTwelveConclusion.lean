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

include model in
/-- Lines of `R₁/T` are normal in `R₁`: `⁅R₁, X⁆ ≤ ⁅R₁, R₁⁆ = T ≤ X`. -/
theorem conj_mem_of_le_of_mem
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) {X : Subgroup G}
    (hTX : fc.sInvertedT model ≤ X) (hXle : X ≤ R₁) {r x : G}
    (hr : r ∈ R₁) (hx : x ∈ X) :
    r * x * r⁻¹ ∈ X := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  have h1 : ⁅r, x⁆ ∈ fc.sInvertedT model := by
    rw [← hcommT]
    exact Subgroup.commutator_mem_commutator hr (hXle hx)
  have h2 : r * x * r⁻¹ = ⁅r, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact mul_mem (hTX h1) hx

omit model in
/-- **`p ∤ [N_G(R₁) : R₁]`**: `R₁` carries the full `p`-part `p³` of `|G|`. -/
theorem not_p_dvd_index_subgroupOf_normalizer_overgroup
    (hfact : (Nat.card G).factorization fc.p = 3) {R₁ : Subgroup G}
    (hcard : Nat.card ↥R₁ = fc.p ^ 3) {N : Subgroup G} (hle : R₁ ≤ N) :
    ¬ fc.p ∣ (R₁.subgroupOf N).index := by
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  intro hdvd
  have h1 := (R₁.subgroupOf N).card_mul_index
  have h2 : Nat.card ↥(R₁.subgroupOf N) = fc.p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  rw [h2] at h1
  obtain ⟨d, hd⟩ := hdvd
  have h3 : fc.p ^ 4 ∣ Nat.card ↥N := by
    refine ⟨d, ?_⟩
    rw [← h1, hd]
    ring
  have h4 : fc.p ^ 4 ∣ Nat.card G :=
    h3.trans (Subgroup.card_subgroup_dvd_card N)
  have h5 := (Nat.Prime.pow_dvd_iff_le_factorization fc.p_prime
    Nat.card_pos.ne').mp h4
  rw [hfact] at h5
  omega

omit model in
/-- **At most `p + 1` lines**: subgroups `T' ≤ Y ≤ A` with `|T'| = p`, `|Y| = p²`,
`|A| = p³` pairwise intersect in `T'`, so the sets `Y ∖ T'` (each of size `p² - p`)
are disjoint inside `A ∖ T'` (of size `p³ - p`). -/
theorem finset_card_lines_le {A T' : Subgroup G} (hT'A : T' ≤ A)
    (hT : Nat.card ↥T' = fc.p) (hA : Nat.card ↥A = fc.p ^ 3)
    (𝒮 : Finset (Subgroup G))
    (hmem : ∀ Y ∈ 𝒮, T' ≤ Y ∧ Y ≤ A ∧ Nat.card ↥Y = fc.p ^ 2) :
    𝒮.card ≤ fc.p + 1 := by
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  haveI := Fintype.ofFinite G
  have hpairinf : ∀ Y ∈ 𝒮, ∀ Y' ∈ 𝒮, Y ≠ Y' → Y ⊓ Y' = T' := by
    intro Y hY Y' hY' hne
    obtain ⟨hTY, hYA, hYc⟩ := hmem Y hY
    obtain ⟨hTY', hY'A, hY'c⟩ := hmem Y' hY'
    have hTinf : T' ≤ Y ⊓ Y' := le_inf hTY hTY'
    have hdvd : Nat.card ↥(Y ⊓ Y') ∣ fc.p ^ 2 := by
      have h1 := Subgroup.card_dvd_of_le (inf_le_left : Y ⊓ Y' ≤ Y)
      rwa [hYc] at h1
    obtain ⟨i, hi2, hicard⟩ := (Nat.dvd_prime_pow fc.p_prime).mp hdvd
    have hge : fc.p ≤ Nat.card ↥(Y ⊓ Y') := by
      have h1 := Subgroup.card_le_of_le hTinf
      rwa [hT] at h1
    have hne2 : Nat.card ↥(Y ⊓ Y') ≠ fc.p ^ 2 := by
      intro h0
      have h1 : Y ⊓ Y' = Y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h0, hYc])
      have h2 : Y ⊓ Y' = Y' :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h0, hY'c])
      exact hne (h1.symm.trans h2)
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
      (by rw [hicard, hi1, hT, pow_one])).symm
  set D : Subgroup G → Finset G :=
    fun Y => (Y : Set G).toFinset \ (T' : Set G).toFinset with hDdef
  have hcardT : (T' : Set G).toFinset.card = fc.p := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hT
  have hDcard : ∀ Y ∈ 𝒮, (D Y).card = fc.p ^ 2 - fc.p := by
    intro Y hY
    obtain ⟨hTY, hYA, hYc⟩ := hmem Y hY
    have h1 : (T' : Set G).toFinset ⊆ (Y : Set G).toFinset := by
      intro x hx
      rw [Set.mem_toFinset] at hx ⊢
      exact hTY hx
    rw [hDdef]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h1, hcardT]
    congr 1
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hYc
  have hdisj : ∀ Y ∈ 𝒮, ∀ Y' ∈ 𝒮, Y ≠ Y' → Disjoint (D Y) (D Y') := by
    intro Y hY Y' hY' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hDdef] at hx hx'
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hx hx'
    have h1 : x ∈ Y ⊓ Y' := ⟨hx.1, hx'.1⟩
    rw [hpairinf Y hY Y' hY' hne] at h1
    exact hx.2 h1
  have hsub : 𝒮.biUnion D ⊆ (A : Set G).toFinset \ (T' : Set G).toFinset := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨Y, hY, hxY⟩ := hx
    obtain ⟨hTY, hYA, -⟩ := hmem Y hY
    rw [hDdef] at hxY
    simp only [Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hxY ⊢
    exact ⟨hYA hxY.1, hxY.2⟩
  have hAcard : ((A : Set G).toFinset \ (T' : Set G).toFinset).card
      = fc.p ^ 3 - fc.p := by
    have h1 : (T' : Set G).toFinset ⊆ (A : Set G).toFinset := by
      intro x hx
      rw [Set.mem_toFinset] at hx ⊢
      exact hT'A hx
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h1, hcardT]
    congr 1
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hA
  have hsum : (𝒮.biUnion D).card = 𝒮.card * (fc.p ^ 2 - fc.p) := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hDcard, Finset.sum_const,
      smul_eq_mul]
  have hle := Finset.card_le_card hsub
  rw [hsum, hAcard] at hle
  have hple : fc.p ≤ fc.p ^ 2 := by
    have := fc.p_prime.one_lt
    nlinarith
  have hple3 : fc.p ≤ fc.p ^ 3 := by
    have := fc.p_prime.one_lt
    nlinarith
  have hpos : 0 < fc.p ^ 2 - fc.p := by
    have h2 := fc.p_prime.one_lt
    have h3 : fc.p < fc.p ^ 2 := by nlinarith
    omega
  have heq : fc.p ^ 3 - fc.p = (fc.p + 1) * (fc.p ^ 2 - fc.p) := by
    zify [hple, hple3]
    ring
  rw [heq] at hle
  exact Nat.le_of_mul_le_mul_right hle hpos

include model in
/-- **`N_G(R₁) = N_G(R)`** ((12) tail, δ4-D): the coset-to-line map
`m·N_G(R) ↦ m•R` is injective into the lines avoiding `T₁`, so
`s' := [N_G(R₁) : N_G(R)] ≤ p`; a proper element `n` spawns `p - 1` distinct
cosets `[k·n]` besides `[1]` (their lines `k•(n•R)` are distinct by the
third-line theorem), so `s' ≥ p`; but `p ∤ s'` since `R₁` carries the full
`p`-part of `|G|`. -/
theorem normalizer_overgroup_eq_normalizer_invImageF
    (ind : Hypothesis.TheoremAInductionBelow G Ω)
    (hB2 : ¬ fc.p ∣ Nat.card (Abelianization G))
    (hm : Nat.card F = fc.p ^ 1)
    (hGp : fc.p ^ (1 + 2) ∣ Nat.card G)
    (hfact : (Nat.card G).factorization fc.p = 3)
    (hSigma : letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
      ¬ fc.p ∣ Nat.card ↥(fc.rankOneQuotient).D) {R₁ : Subgroup G}
    (hRle : fc.invImageF model ≤ R₁)
    (hR₁le : R₁ ≤ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G))
    (hcard : Nat.card ↥R₁ = fc.p ^ 3)
    (hR₁n : ∀ n ∈ Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G),
      ∀ x ∈ R₁, n * x * n⁻¹ ∈ R₁) :
    Subgroup.normalizer ((R₁ : Subgroup G) : Set G)
      = Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) := by
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  classical
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  set NR : Subgroup G :=
    Subgroup.normalizer ((fc.invImageF model : Subgroup G) : Set G) with hNRdef
  set N : Subgroup G := Subgroup.normalizer ((R₁ : Subgroup G) : Set G) with hNdef
  obtain ⟨hTle, hTinv, -, -⟩ := fc.sInvertedT_spec model ind hB2 hm
  have hTcard : Nat.card ↥(fc.sInvertedT model) = fc.p := by
    rw [fc.card_sInvertedT model ind hB2 hm, hm, pow_one]
  have hRcard : Nat.card ↥(fc.invImageF model) = fc.p ^ 2 := by
    rw [fc.card_invImageF model ind, hm, pow_one, fc.card_P, pow_two]
  have hcommT := fc.commutator_eq_sInvertedT model ind hB2 hm hGp hSigma hRle
    hR₁le hcard
  obtain ⟨hT₁card, hTsubT₁, hT₁infP⟩ := fc.card_sInvertedOvergroup model ind hB2 hm
    hGp hSigma hRle hR₁le hcard hR₁n
  have hT₁le : fc.sInvertedOvergroup R₁ ≤ R₁ := fun x hx =>
    ((fc.mem_sInvertedOvergroup_iff model ind hB2 hm hGp hSigma hRle hR₁le
      hcard).mp hx).1
  -- `N_G(R) ≤ N_G(R₁)`.
  have hNRle : NR ≤ N := by
    intro k hk
    rw [hNdef, Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hR₁n k hk x hx
    · intro hx
      have h1 := hR₁n k⁻¹ (Subgroup.inv_mem _ hk) _ hx
      simpa [mul_assoc] using h1
  apply le_antisymm ?_ hNRle
  by_contra hnle
  obtain ⟨n, hnN, hnNR⟩ := SetLike.not_le_iff_exists.mp hnle
  -- every `m ∈ N` fixes `T` setwise and sends `R` to a line.
  have hmT : ∀ m ∈ N, MulAut.conj m • fc.sInvertedT model = fc.sInvertedT model := by
    intro m hm
    have h1 : MulAut.conj m • R₁ = R₁ := conj_smul_eq_iff_mem_normalizer.mpr hm
    have h2 : MulAut.conj m • ⁅R₁, R₁⁆ = ⁅R₁, R₁⁆ := by
      rw [Subgroup.pointwise_smul_def, Subgroup.map_commutator]
      rw [show R₁.map ((MulDistribMulAction.toMonoidEnd (MulAut G) G)
          (MulAut.conj m)) = R₁ from h1]
    rw [← hcommT]
    exact h2
  have hline : ∀ m ∈ N,
      fc.sInvertedT model ≤ MulAut.conj m • fc.invImageF model ∧
      MulAut.conj m • fc.invImageF model ≤ R₁ ∧
      Nat.card ↥(MulAut.conj m • fc.invImageF model) = fc.p ^ 2 := by
    intro m hm
    refine ⟨?_, ?_, ?_⟩
    · have h1 : MulAut.conj m • fc.sInvertedT model
          ≤ MulAut.conj m • fc.invImageF model :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hTle
      rwa [hmT m hm] at h1
    · have h1 : MulAut.conj m • fc.invImageF model ≤ MulAut.conj m • R₁ :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hRle
      rwa [conj_smul_eq_iff_mem_normalizer.mpr hm] at h1
    · rw [← hRcard]
      exact (Nat.card_congr
        (Subgroup.equivSMul (MulAut.conj m) (fc.invImageF model)).toEquiv).symm
  -- the coset-to-line map `Φ`.
  haveI := Fintype.ofFinite (↥N ⧸ NR.subgroupOf N)
  set Φ : (↥N ⧸ NR.subgroupOf N) → Subgroup G :=
    Quotient.lift (fun m : ↥N => MulAut.conj (m : G) • fc.invImageF model)
      (by
        intro a b hab
        have h1 : (a : G)⁻¹ * (b : G) ∈ NR := by
          have h2 := (QuotientGroup.leftRel_apply).mp hab
          have h3 := Subgroup.mem_subgroupOf.mp h2
          simpa using h3
        have h3 : MulAut.conj ((a : G)⁻¹ * (b : G)) • fc.invImageF model
            = fc.invImageF model := conj_smul_eq_iff_mem_normalizer.mpr h1
        have h4 : MulAut.conj (b : G) • fc.invImageF model
            = MulAut.conj (a : G) • (MulAut.conj ((a : G)⁻¹ * (b : G))
              • fc.invImageF model) := by
          rw [← mul_smul, ← map_mul]
          congr 2
          group
        rw [h3] at h4
        exact h4.symm) with hΦdef
  have hΦmk : ∀ m : ↥N, Φ (QuotientGroup.mk m)
      = MulAut.conj (m : G) • fc.invImageF model := fun m => rfl
  have hΦinj : Function.Injective Φ := by
    intro qa qb h
    obtain ⟨a, rfl⟩ := Quotient.exists_rep qa
    obtain ⟨b, rfl⟩ := Quotient.exists_rep qb
    have h1 : MulAut.conj (a : G) • fc.invImageF model
        = MulAut.conj (b : G) • fc.invImageF model := h
    have h2 : MulAut.conj ((b : G)⁻¹ * (a : G)) • fc.invImageF model
        = fc.invImageF model := by
      rw [map_mul, mul_smul, h1, ← mul_smul, ← map_mul, inv_mul_cancel, map_one,
        one_smul]
    have h3 : (b : G)⁻¹ * (a : G) ∈ NR := conj_smul_eq_iff_mem_normalizer.mp h2
    apply Quotient.sound
    refine (QuotientGroup.leftRel_apply).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have h4 : ((a⁻¹ * b : ↥N) : G) = (a : G)⁻¹ * (b : G) := by simp
    rw [h4]
    have h5 := NR.inv_mem h3
    simpa using h5
  -- upper bound: `s' ≤ p`.
  set 𝒮₀ : Finset (Subgroup G) := Finset.image Φ Finset.univ with h𝒮₀def
  have h𝒮₀card : 𝒮₀.card = Nat.card (↥N ⧸ NR.subgroupOf N) := by
    rw [h𝒮₀def, Finset.card_image_of_injective _ hΦinj, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hT₁not : fc.sInvertedOvergroup R₁ ∉ 𝒮₀ := by
    intro h0
    rw [h𝒮₀def, Finset.mem_image] at h0
    obtain ⟨q, -, hq⟩ := h0
    obtain ⟨m, rfl⟩ := Quotient.exists_rep q
    rw [hΦmk] at hq
    exact fc.conj_invImageF_ne_sInvertedOvergroup model ind hB2 hm hGp hSigma hRle
      hR₁le hcard (m : G) hq
  have hupper : Nat.card (↥N ⧸ NR.subgroupOf N) ≤ fc.p := by
    have h1 := fc.finset_card_lines_le (hT'A := hTle.trans hRle)
      hTcard hcard (insert (fc.sInvertedOvergroup R₁) 𝒮₀) ?_
    · rw [Finset.card_insert_of_notMem hT₁not, h𝒮₀card] at h1
      omega
    · intro Y hY
      rw [Finset.mem_insert] at hY
      rcases hY with rfl | hY
      · exact ⟨hTsubT₁, hT₁le, hT₁card⟩
      · rw [h𝒮₀def, Finset.mem_image] at hY
        obtain ⟨q, -, rfl⟩ := hY
        obtain ⟨m, rfl⟩ := Quotient.exists_rep q
        rw [hΦmk]
        exact hline (m : G) m.2
  -- lower bound: `s' ≥ p` via the `[k·n]`-family.
  haveI := Fintype.ofFinite (↥NR ⧸ R₁.subgroupOf NR)
  set ψ : (↥NR ⧸ R₁.subgroupOf NR) → (↥N ⧸ NR.subgroupOf N) :=
    Quotient.lift (fun k : ↥NR => (QuotientGroup.mk
        (⟨(k : G) * n, mul_mem (hNRle k.2) hnN⟩ : ↥N) : ↥N ⧸ NR.subgroupOf N))
      (by
        intro a b hab
        have h1 : (a : G)⁻¹ * (b : G) ∈ R₁ := by
          have h2 := (QuotientGroup.leftRel_apply).mp hab
          have h3 := Subgroup.mem_subgroupOf.mp h2
          simpa using h3
        apply Quotient.sound
        refine (QuotientGroup.leftRel_apply).mpr ?_
        rw [Subgroup.mem_subgroupOf]
        have h4 : (((⟨(a : G) * n, mul_mem (hNRle a.2) hnN⟩ : ↥N)⁻¹
            * (⟨(b : G) * n, mul_mem (hNRle b.2) hnN⟩ : ↥N) : ↥N) : G)
            = n⁻¹ * ((a : G)⁻¹ * (b : G)) * n := by
          change ((a : G) * n)⁻¹ * ((b : G) * n)
            = n⁻¹ * ((a : G)⁻¹ * (b : G)) * n
          group
        rw [h4]
        -- `n⁻¹ R₁ n = R₁ ≤ N_G(R)`.
        have h5 : n⁻¹ * ((a : G)⁻¹ * (b : G)) * n ∈ R₁ := by
          have h6 := (Subgroup.mem_set_normalizer_iff.mp hnN
            (n⁻¹ * ((a : G)⁻¹ * (b : G)) * n)).mpr ?_
          · exact h6
          · have h7 : n * (n⁻¹ * ((a : G)⁻¹ * (b : G)) * n) * n⁻¹
                = (a : G)⁻¹ * (b : G) := by group
            rw [h7]
            exact h1
        exact hR₁le h5) with hψdef
  have hψmk : ∀ k : ↥NR, ψ (QuotientGroup.mk k)
      = (QuotientGroup.mk (⟨(k : G) * n, mul_mem (hNRle k.2) hnN⟩ : ↥N)) :=
    fun k => rfl
  -- `X := n•R` is a line distinct from `R` and `T₁`.
  have hXprops := hline n hnN
  have hXneR : MulAut.conj n • fc.invImageF model ≠ fc.invImageF model := by
    intro h0
    exact hnNR (conj_smul_eq_iff_mem_normalizer.mp h0)
  have hXneT₁ : MulAut.conj n • fc.invImageF model ≠ fc.sInvertedOvergroup R₁ :=
    fc.conj_invImageF_ne_sInvertedOvergroup model ind hB2 hm hGp hSigma hRle hR₁le
      hcard n
  have hψinj : Function.Injective ψ := by
    intro qa qb h
    obtain ⟨a, rfl⟩ := Quotient.exists_rep qa
    obtain ⟨b, rfl⟩ := Quotient.exists_rep qb
    rw [hψmk, hψmk] at h
    -- pass through `Φ`: the lines `a•X` and `b•X` coincide.
    have h1 := congrArg Φ h
    rw [hΦmk, hΦmk] at h1
    simp only at h1
    -- `(b⁻¹ a)` fixes the line `X`.
    have h2 : MulAut.conj ((b : G)⁻¹ * (a : G))
        • (MulAut.conj n • fc.invImageF model)
        = MulAut.conj n • fc.invImageF model := by
      rw [map_mul, mul_smul]
      have h3 : MulAut.conj (a : G) • (MulAut.conj n • fc.invImageF model)
          = MulAut.conj (b : G) • (MulAut.conj n • fc.invImageF model) := by
        rw [← mul_smul, ← map_mul, ← mul_smul, ← map_mul]
        exact h1
      rw [h3, ← mul_smul, ← map_mul, ← mul_smul, ← map_mul]
      have h4 : (b : G)⁻¹ * (b : G) * n = n := by group
      rw [h4]
    have h5 : (b : G)⁻¹ * (a : G) ∈ R₁ :=
      fc.mem_of_conj_smul_eq_of_ne model ind hB2 hm hGp hSigma hRle hR₁le hcard
        hR₁n hXprops.1 hXprops.2.1 hXprops.2.2 hXneR hXneT₁
        (mul_mem (NR.inv_mem b.2) a.2) h2
    apply Quotient.sound
    refine (QuotientGroup.leftRel_apply).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have h6 : ((a⁻¹ * b : ↥NR) : G) = (a : G)⁻¹ * (b : G) := by simp
    rw [h6]
    have h7 := R₁.inv_mem h5
    simpa using h7
  have hone_not : (QuotientGroup.mk (1 : ↥N) : ↥N ⧸ NR.subgroupOf N)
      ∉ Set.range ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨k, rfl⟩ := Quotient.exists_rep q
    rw [hψmk] at hq
    have h1 : (1 : ↥N)⁻¹ * (⟨(k : G) * n, mul_mem (hNRle k.2) hnN⟩ : ↥N)
        ∈ NR.subgroupOf N := QuotientGroup.eq.mp hq.symm
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (k : G) * n ∈ NR := by simpa using h1
    have h3 : n ∈ NR := by
      have h4 : n = (k : G)⁻¹ * ((k : G) * n) := by group
      rw [h4]
      exact mul_mem (NR.inv_mem k.2) h2
    exact hnNR h3
  -- `|NR/R₁| = p - 1`.
  have hNRcard : Nat.card ↥NR = fc.p ^ 3 * (fc.p - 1) := by
    have h1 := ((fc.invImageF model).subgroupOf NR).card_mul_index
    have h2 : Nat.card ↥((fc.invImageF model).subgroupOf NR)
        = Nat.card ↥(fc.invImageF model) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
    have h3 : ((fc.invImageF model).subgroupOf NR).index = fc.p * (fc.p - 1) :=
      fc.card_quotient_invImageF_eq model ind hB2 hm hGp hSigma
    rw [h2, h3, hRcard] at h1
    rw [← h1]
    ring
  have hquotcard : Nat.card (↥NR ⧸ R₁.subgroupOf NR) = fc.p - 1 := by
    have h1 := (R₁.subgroupOf NR).card_mul_index
    have h2 : Nat.card ↥(R₁.subgroupOf NR) = fc.p ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₁le).toEquiv, hcard]
    rw [h2, hNRcard] at h1
    have h3 : (R₁.subgroupOf NR).index
        = Nat.card (↥NR ⧸ R₁.subgroupOf NR) := rfl
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero
      (by have := fc.p_prime.pos; positivity)) h1
  have hlower : fc.p ≤ Nat.card (↥N ⧸ NR.subgroupOf N) := by
    have h1 : Nat.card (↥NR ⧸ R₁.subgroupOf NR)
        ≤ Nat.card {q : ↥N ⧸ NR.subgroupOf N // q ∈ Set.range ψ} := by
      refine Nat.card_le_card_of_injective
        (fun q => ⟨ψ q, Set.mem_range_self q⟩) ?_
      intro q q' hqq
      exact hψinj (congrArg Subtype.val hqq)
    have h2 : Nat.card {q : ↥N ⧸ NR.subgroupOf N // q ∈ Set.range ψ} + 1
        ≤ Nat.card (↥N ⧸ NR.subgroupOf N) := by
      classical
      have h3 : (Set.range ψ).ncard + 1 ≤ Nat.card (↥N ⧸ NR.subgroupOf N) := by
        have h4 : insert (QuotientGroup.mk (1 : ↥N) : ↥N ⧸ NR.subgroupOf N)
            (Set.range ψ) ⊆ Set.univ := Set.subset_univ _
        have h5 := Set.ncard_le_ncard h4 (Set.toFinite _)
        rw [Set.ncard_insert_of_notMem hone_not (Set.toFinite _),
          Set.ncard_univ] at h5
        exact h5
      rwa [← Nat.card_coe_set_eq] at h3
    have h4 := le_trans (Nat.add_le_add_right h1 1) h2
    rw [hquotcard] at h4
    have h5 := fc.p_prime.pos
    omega
  -- `p ∤ s'`.
  have hpnot : ¬ fc.p ∣ Nat.card (↥N ⧸ NR.subgroupOf N) := by
    intro hdvd
    have h1 : (NR.subgroupOf N).index = Nat.card (↥N ⧸ NR.subgroupOf N) := rfl
    have h2 : (R₁.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h3 : (NR.subgroupOf N).index ∣ (R₁.subgroupOf N).index := by
      refine Subgroup.index_dvd_of_le ?_
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hR₁le hx
    have h4 : fc.p ∣ (R₁.subgroupOf N).index := by
      refine dvd_trans ?_ h3
      rw [h1]
      exact hdvd
    exact fc.not_p_dvd_index_subgroupOf_normalizer_overgroup hfact hcard
      (hR₁le.trans hNRle) h4
  -- squeeze.
  have hfinal : Nat.card (↥N ⧸ NR.subgroupOf N) = fc.p := le_antisymm hupper hlower
  exact hpnot (hfinal ▸ dvd_refl fc.p)

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
